use crate::{
    delta_q::{expand_gossip, DeltaQ, LoadUpdate, Name},
    DeltaQExpr, Outcome, PersistentContext,
};
use std::{collections::BTreeSet, rc::Rc, sync::Arc};
use web_sys::HtmlInputElement;
use yew::prelude::*;

/// A piece of context that tells the DeltaQ rendering components to which named expression they belong.
#[derive(Clone, PartialEq)]
pub struct DeltaQContext {
    pub eval_ctx: Rc<PersistentContext>,
    pub name: String,
}

impl DeltaQContext {
    pub fn new(eval_ctx: &PersistentContext, name: &str) -> Self {
        Self {
            eval_ctx: Rc::new(eval_ctx.clone()),
            name: name.to_owned(),
        }
    }
}

#[derive(Properties, Clone, PartialEq, Debug)]
pub struct Props {
    pub delta_q: Arc<DeltaQExpr>,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(DeltaQComponent)]
pub fn delta_q_component(props: &Props) -> Html {
    // web_sys::console::log_1(&wasm_bindgen::JsValue::from_str(&format!("{props:?}")));
    let on_change = props.on_change.clone();
    match &*props.delta_q {
        DeltaQExpr::BlackBox => {
            html! { <BlackBox {on_change} /> }
        }
        DeltaQExpr::Name(name, rec) => {
            html! { <NameComponent name={(&**name).to_owned()} rec={*rec} {on_change} /> }
        }
        DeltaQExpr::Outcome(outcome) => {
            html! { <CdfComponent outcome={outcome.clone()} {on_change} /> }
        }
        DeltaQExpr::Seq(first, load, second) => {
            html!(<Seq first={first.clone()} load={load.clone()} second={second.clone()} {on_change} />)
        }
        DeltaQExpr::Choice(first, first_weight, second, second_weight) => {
            html!(<Branch top={first.clone()} bottom={second.clone()} {on_change} kind={BranchKind::Choice(*first_weight, *second_weight)} />)
        }
        DeltaQExpr::ForAll(first, second) => {
            html!(<Branch top={first.clone()} bottom={second.clone()} kind={BranchKind::ForAll} {on_change} />)
        }
        DeltaQExpr::ForSome(first, second) => {
            html!(<Branch top={first.clone()} bottom={second.clone()} kind={BranchKind::ForSome} {on_change} />)
        }
        DeltaQExpr::Gossip {
            send,
            receive,
            size,
            branching,
            cluster_coeff,
            disjoint_names,
        } => {
            html! { <Gossip send={send.clone()} receive={receive.clone()} size={*size} branching={*branching} cluster_coeff={*cluster_coeff} disjoint_names={disjoint_names.clone()} {on_change} /> }
        }
        DeltaQExpr::Min(outcomes) => {
            html! { <Min outcomes={outcomes.clone()} label="MIN" {on_change} /> }
        }
        DeltaQExpr::Max(outcomes) => {
            html! { <Min outcomes={outcomes.clone()} label="MAX" {on_change} /> }
        }
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct BlackBoxProps {
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(BlackBox)]
pub fn black_box(props: &BlackBoxProps) -> Html {
    let on_change = props.on_change.clone();
    let popup = use_state(|| false);
    let ctx = use_context::<DeltaQContext>().unwrap();

    let name = use_state(|| "".to_string());
    let oninput = Callback::from(cloned!(name; move |e: InputEvent| {
        name.set(e.target_unchecked_into::<HtmlInputElement>().value());
    }));
    let onsubmit = Callback::from(cloned!(name, on_change, ctx;
        move |e: SubmitEvent| {
            e.prevent_default();
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&name).arc())));
        }
    ));

    html! {
        <div class={classes!("blackBox", "anchor")} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
            if *popup {
                <div class={classes!("popup")}>
                    <button onclick={cloned!(popup; move |_| popup.set(false))}>{ "abort" }</button>
                    <form {onsubmit}>
                        <input type="submit" value="refine" />
                        <input type="text" value={(*name).clone()} {oninput} />
                    </form>
                </div>
            }
        </div>
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct NameProps {
    pub name: String,
    pub rec: Option<usize>,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(NameComponent)]
pub fn name_component(props: &NameProps) -> Html {
    let on_change = props.on_change.clone();
    let popup = use_state(|| false);
    let name = props.name.clone();
    let rec = props.rec;
    let ctx = use_context::<DeltaQContext>().unwrap();

    let new_name = use_state(|| props.name.clone());
    let oninput = Callback::from(cloned!(new_name; move |e: InputEvent| {
        new_name.set(e.target_unchecked_into::<HtmlInputElement>().value());
    }));
    let onsubmit = Callback::from(cloned!(new_name, on_change, ctx, popup;
        move |e: SubmitEvent| {
            e.prevent_default();
            popup.set(false);
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name_rec(&new_name, rec).arc())));
        }
    ));

    use_effect_with(
        popup.clone(),
        cloned!(new_name, name; move |popup| {
            if **popup {
                new_name.set(name.clone());
            }
        }),
    );

    html! {
        <div class={classes!("name", "anchor")} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
            { &props.name }
            if let Some(rec) = rec { <sup>{ rec }</sup> }
            if *popup {
                <div class={classes!("popup")}>
                    <button onclick={cloned!(popup;
                        move |_| popup.set(false))}>{ "abort" }</button>
                    <form {onsubmit}>
                        <input type="submit" value="change" />
                        <input type="text" value={(*new_name).clone()} {oninput} />
                    </form>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::seq(DeltaQ::name(&name), LoadUpdate::default(), DeltaQExpr::BlackBox.into()).arc())))) }>{ "append" }</button>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(DeltaQ::name(&name), 1.0, DeltaQExpr::BlackBox.into(), 1.0).arc())))) }>{ "make choice" }</button>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_all(DeltaQ::name(&name), DeltaQExpr::BlackBox.into()).arc())))) }>{ "make forAll" }</button>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_some(DeltaQ::name(&name), DeltaQExpr::BlackBox.into()).arc())))) }>{ "make forSome" }</button>
                    <button onclick={cloned!(on_change, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQExpr::BlackBox.into()))))}>{ "black box" }</button>
                    <button onclick={cloned!(on_change, ctx, popup, name;
                        move |_| { popup.set(false); if let Some(dq) = ctx.eval_ctx.get(&name) { on_change.emit((ctx.name.clone(), Some(dq.arc()))) } })}>{ "inline" }</button>
                </div>
            }
        </div>
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct CdfProps {
    pub outcome: Outcome,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(CdfComponent)]
pub fn cdf_component(props: &CdfProps) -> Html {
    let outcome = props.outcome.clone();
    let on_change = props.on_change.clone();
    let popup = use_state(|| false);
    let ctx = use_context::<DeltaQContext>().unwrap();

    let abstract_name = use_state(|| "".to_string());
    let abstract_input = Callback::from(cloned!(abstract_name;
        move |e: InputEvent| abstract_name.set(e.target_unchecked_into::<HtmlInputElement>().value())));
    let abstract_submit = Callback::from(cloned!(abstract_name, on_change, ctx, outcome;
        move |e: SubmitEvent| {
            e.prevent_default();
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&abstract_name).arc())));
            on_change.emit(((*abstract_name).clone(), Some(DeltaQExpr::Outcome(outcome.clone()).into())));
        }
    ));

    html! {
        <div class={classes!("cdf", "anchor")} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
            { format!("{:#}", props.outcome) }
            if *popup {
                <div class={classes!("popup")}>
                    <button onclick={cloned!(popup; move |_| popup.set(false))}>{ "abort" }</button>
                    <button onclick={cloned!(on_change, outcome, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::seq(DeltaQExpr::Outcome(outcome.clone()).into(), LoadUpdate::default(), DeltaQExpr::BlackBox.into()).arc())))) }>{ "append" }</button>
                    <button onclick={cloned!(on_change, outcome, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(DeltaQExpr::Outcome(outcome.clone()).into(), 1.0, DeltaQExpr::BlackBox.into(), 1.0).arc())))) }>{ "make choice" }</button>
                    <button onclick={cloned!(on_change, outcome, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_all(DeltaQExpr::Outcome(outcome.clone()).into(), DeltaQExpr::BlackBox.into()).arc())))) }>{ "make forAll" }</button>
                    <button onclick={cloned!(on_change, outcome, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_some(DeltaQExpr::Outcome(outcome.clone()).into(), DeltaQExpr::BlackBox.into()).arc())))) }>{ "make forSome" }</button>
                    <button onclick={cloned!(on_change, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQExpr::BlackBox.into()))))}>{ "black box" }</button>
                    <form onsubmit={abstract_submit}>
                        <input type="submit" value="abstract" />
                        <input type="text" value={(*abstract_name).clone()} oninput={abstract_input} />
                    </form>
                </div>
            }
        </div>
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct SeqProps {
    pub first: Arc<DeltaQExpr>,
    pub load: LoadUpdate,
    pub second: Arc<DeltaQExpr>,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(Seq)]
pub fn seq(props: &SeqProps) -> Html {
    let on_change = props.on_change.clone();
    let first = props.first.clone();
    let second = props.second.clone();
    let load = props.load.clone();
    let ctx = use_context::<DeltaQContext>().unwrap();

    let on_first_change = Callback::from(cloned!(second, on_change, ctx, load;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(DeltaQExpr::Seq(delta_q, load.clone(), second.clone()).into())));
            }
        }
    ));

    let on_second_change = Callback::from(cloned!(first, on_change, ctx, load;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(DeltaQExpr::Seq(first.clone(), load.clone(), delta_q).into())));
            }
        }
    ));

    let popup = use_state(|| false);
    let name = use_state(|| "".to_string());
    let oninput = Callback::from(cloned!(name; move |e: InputEvent| {
        name.set(e.target_unchecked_into::<HtmlInputElement>().value());
    }));
    let onsubmit = Callback::from(cloned!(name, on_change, ctx, first, second, load;
        move |e: SubmitEvent| {
            e.prevent_default();
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&name).arc())));
            on_change.emit(((*name).clone(), Some(DeltaQExpr::Seq(first.clone(), load.clone(), second.clone()).into())));
        }
    ));

    html! {
        <div class={classes!("row", "center", "frame")}>
            <DeltaQComponent delta_q={first.clone()} on_change={on_first_change} />
            <div class={classes!("seqSymbol", "anchor", (!load.disjoint_names.is_empty()).then_some("disjoint"))} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
                { format!("{}", load) }
                if *popup {
                    <div class={classes!("popup")}>
                    <button onclick={cloned!(popup;
                        move |_| popup.set(false))}> { "abort" } </button>
                    <button onclick={cloned!(on_change, first, second, ctx, load;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(DeltaQExpr::Seq(first.clone(), load.clone(), second.clone()).into(), 1.0, DeltaQExpr::BlackBox.into(), 1.0).arc()))))}> { "make choice" } </button>
                    <button onclick={cloned!(on_change, first, second, ctx, load;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_all(DeltaQExpr::Seq(first.clone(), load.clone(), second.clone()).into(), DeltaQExpr::BlackBox.into()).arc()))))}> { "make forAll" } </button>
                    <button onclick={cloned!(on_change, first, second, ctx, load;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_some(DeltaQExpr::Seq(first.clone(), load.clone(), second.clone()).into(), DeltaQExpr::BlackBox.into()).arc()))))}> { "make forSome" } </button>
                    <button onclick={cloned!(on_change, first, second, popup, ctx, load;
                        move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(DeltaQExpr::Seq(second.clone(), load.clone(), first.clone()).into()))) })}>{ "switch" }</button>
                    <button onclick={cloned!(on_change, first, second, ctx, load;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQExpr::Seq(first.clone(), load.clone(), second.clone()).into()))))}>{ "append" }</button>
                    <button onclick={cloned!(popup, on_change, first, ctx;
                        move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(first.clone()))) })}>{ "keep left" }</button>
                    <button onclick={cloned!(popup, on_change, second, ctx;
                        move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(second.clone()))) })}>{ "keep right" }</button>
                    <button onclick={cloned!(on_change, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQExpr::BlackBox.into()))))}>{ "black box" }</button>
                    <form {onsubmit}>
                        <input type="submit" value="abstract" />
                        <input type="text" value={(*name).clone()} {oninput} />
                    </form>
                    </div>
                }
            </div>
            <DeltaQComponent delta_q={second} on_change={on_second_change} />
        </div>
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct BranchProps {
    pub top: Arc<DeltaQExpr>,
    pub bottom: Arc<DeltaQExpr>,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
    pub kind: BranchKind,
}

#[derive(Clone, Copy, PartialEq)]
pub enum BranchKind {
    Choice(f32, f32),
    ForAll,
    ForSome,
}

impl BranchKind {
    pub fn choice_frac(&self) -> (f32, f32) {
        match self {
            BranchKind::Choice(l, r) => (*l, *r),
            _ => (1.0, 1.0),
        }
    }
}

#[function_component(BranchKindComponent)]
pub fn branch_kind_component(props: &BranchProps) -> Html {
    let kind = props.kind;
    let kind_html = match kind {
        BranchKind::Choice(first_weight, second_weight) => html! {
            <div class={classes!("column", "center")}>
                <div>{first_weight}</div>
                <div>{"⇌"}</div>
                <div>{second_weight}</div>
            </div>
        },
        BranchKind::ForAll => html! { <div>{ "∀" }</div> },
        BranchKind::ForSome => html! { <div>{ "∃" }</div> },
    };

    let popup = use_state(|| false);
    let on_change = props.on_change.clone();
    let top = props.top.clone();
    let bottom = props.bottom.clone();
    let ctx = use_context::<DeltaQContext>().unwrap();

    let top_frac = use_state(|| props.kind.choice_frac().0);
    let bottom_frac = use_state(|| props.kind.choice_frac().1);
    let top_input = Callback::from(cloned!(top_frac; move |e: InputEvent| {
        if let Ok(f) = e.target_unchecked_into::<HtmlInputElement>().value().parse::<f32>() {
            top_frac.set(f);
        }
    }));
    let bottom_input = Callback::from(cloned!(bottom_frac; move |e: InputEvent| {
        if let Ok(f) = e.target_unchecked_into::<HtmlInputElement>().value().parse::<f32>() {
            bottom_frac.set(f);
        }
    }));
    let frac_submit = Callback::from(
        cloned!(popup, on_change, top, bottom, top_frac, bottom_frac, ctx;
        move |e: SubmitEvent| {
            e.prevent_default();
            popup.set(false);
            on_change.emit((ctx.name.clone(), Some(DeltaQExpr::Choice(top.clone(), *top_frac, bottom.clone(), *bottom_frac).into())));
        }),
    );

    let choices = props.kind.choice_frac();
    use_effect_with(
        popup.clone(),
        cloned!(top_frac, bottom_frac; move |popup| {
            if **popup {
                top_frac.set(choices.0);
                bottom_frac.set(choices.1);
            }
        }),
    );

    let abstract_name = use_state(|| "".to_string());
    let abstract_input = Callback::from(cloned!(abstract_name;
        move |e: InputEvent| abstract_name.set(e.target_unchecked_into::<HtmlInputElement>().value())));
    let abstract_submit = Callback::from(cloned!(abstract_name, on_change, ctx, bottom, top;
        move |e: SubmitEvent| {
            e.prevent_default();
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&abstract_name).arc())));
            on_change.emit(((*abstract_name).clone(), Some(mk_branch(kind, top.clone(), bottom.clone()))));
        }
    ));

    html!(
    <div class={classes!("row", "center", "branchKind", "anchor")} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
        { kind_html }
        if *popup {
            <div class={classes!("popup")}>
                <button onclick={cloned!(popup; move |_| popup.set(false))}>{ "abort" }</button>
                <form onsubmit={frac_submit}>
                    <input type="submit" value="make choice" />
                    <input type="number" value={top_frac.to_string()} oninput={top_input} />
                    <input type="number" value={bottom_frac.to_string()} oninput={bottom_input} />
                </form>
                <button onclick={cloned!(popup, on_change, top, bottom, ctx; move |_| {
                    popup.set(false);
                    on_change.emit((ctx.name.clone(), Some(DeltaQExpr::ForAll(top.clone(), bottom.clone()).into())))
                })}>{ "make forAll" }</button>
                <button onclick={cloned!(popup, on_change, top, bottom, ctx; move |_| {
                    popup.set(false);
                    on_change.emit((ctx.name.clone(), Some(DeltaQExpr::ForSome(top.clone(), bottom.clone()).into())))
                })}>{ "make forSome" }</button>
                <button onclick={cloned!(popup, on_change, top, bottom, ctx; move |_| {
                    popup.set(false);
                    on_change.emit((ctx.name.clone(), Some(mk_branch(kind, bottom.clone(), top.clone()))))
                })}>{ "switch" }</button>
                <button onclick={cloned!(popup, on_change, top, bottom, ctx;
                    move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(DeltaQExpr::Seq(mk_branch(kind, top.clone(), bottom.clone()), LoadUpdate::default(), DeltaQExpr::BlackBox.into()).into()))) })}>{ "append" }</button>
                <button onclick={cloned!(popup, on_change, top, ctx;
                    move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(top.clone()))) })}>{ "keep top" }</button>
                <button onclick={cloned!(popup, on_change, bottom, ctx;
                    move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(bottom.clone()))) })}>{ "keep bottom" }</button>
                <button onclick={cloned!(on_change, ctx;
                    move |_| on_change.emit((ctx.name.clone(), Some(DeltaQExpr::BlackBox.into()))))}>{ "black box" }</button>
                <form onsubmit={abstract_submit}>
                    <input type="submit" value="abstract" />
                    <input type="text" value={(*abstract_name).clone()} oninput={abstract_input} />
                </form>
            </div>
        }
    </div>)
}

fn mk_branch(kind: BranchKind, top: Arc<DeltaQExpr>, bottom: Arc<DeltaQExpr>) -> Arc<DeltaQExpr> {
    match kind {
        BranchKind::Choice(l, r) => DeltaQExpr::Choice(top, l, bottom, r).into(),
        BranchKind::ForAll => DeltaQExpr::ForAll(top, bottom).into(),
        BranchKind::ForSome => DeltaQExpr::ForSome(top, bottom).into(),
    }
}

/// A component that renders a branch of a DeltaQ tree.
///
/// The HTML representation consists of two DIV, with the left showing the branch kind and the right showing the branch content.
/// The branch content is rendered in two DIV, the top branch at the top and the bottom branch at the bottom.
/// There is a border between the two branches and to the right of the branch kind.
#[function_component(Branch)]
fn branch(props: &BranchProps) -> Html {
    let on_change = props.on_change.clone();
    let top = props.top.clone();
    let bottom = props.bottom.clone();
    let kind = props.kind;
    let ctx = use_context::<DeltaQContext>().unwrap();

    let on_top_change = Callback::from(cloned!(bottom, on_change, ctx;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(mk_branch(kind, delta_q, bottom.clone()))));
            }
        }
    ));

    let on_bottom_change = Callback::from(cloned!(top, on_change, ctx;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(mk_branch(kind, top.clone(), delta_q))));
            }
        }
    ));

    html! {
        <div class={classes!("row", "frame")}>
            <BranchKindComponent ..props.clone() />
            <div class={classes!("column", "left")} style="border-left: 2px solid black;">
                <div class={classes!("row", "left")} >
                    <DeltaQComponent delta_q={top} on_change={on_top_change} />
                </div>
                <div style="border: 1px solid black;"></div>
                <div class={classes!("row", "left")} >
                    <DeltaQComponent delta_q={bottom} on_change={on_bottom_change} />
                </div>
            </div>
        </div>
    }
}

pub enum EvalCtxAction {
    Put(String, DeltaQ),
    Remove(String),
    Set(PersistentContext),
    ToggleConstraint(Name),
    EditConstraint(Name, String),
}

impl Reducible for PersistentContext {
    type Action = EvalCtxAction;

    fn reduce(self: Rc<Self>, act: Self::Action) -> Rc<Self> {
        match act {
            EvalCtxAction::Put(name, delta_q) => {
                let mut ret = (*self).clone();
                ret.put(name, delta_q);
                Rc::new(ret)
            }
            EvalCtxAction::Remove(name) => {
                let mut ret = (*self).clone();
                ret.remove(&name);
                Rc::new(ret)
            }
            EvalCtxAction::Set(evaluation_context) => Rc::new(evaluation_context),
            EvalCtxAction::ToggleConstraint(name) => {
                let mut ret = (*self).clone();
                if ret.constraint(&name).is_some() {
                    ret.set_constraint(&name, None);
                } else {
                    ret.set_constraint(&name, Some("".into()));
                }
                Rc::new(ret)
            }
            EvalCtxAction::EditConstraint(name, value) => {
                let mut ret = (*self).clone();
                ret.set_constraint(&name, Some(value.into()));
                Rc::new(ret)
            }
        }
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct GossipProps {
    pub send: Arc<DeltaQExpr>,
    pub receive: Arc<DeltaQExpr>,
    pub size: f32,
    pub branching: f32,
    pub cluster_coeff: f32,
    pub disjoint_names: BTreeSet<Name>,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(Gossip)]
pub fn gossip(props: &GossipProps) -> Html {
    let GossipProps {
        send,
        receive,
        size,
        branching,
        cluster_coeff,
        disjoint_names,
        on_change: _,
    } = props;

    let popup = use_state(|| false);
    let toggle_popup = Callback::from(cloned!(popup; move |_| popup.set(!*popup)));

    html! {
        <div class={classes!("frame")} onclick={toggle_popup}>
            { format!("gossip({send}, {receive}, {size}, {branching}, {cluster_coeff})") }
            if *popup {
                <div class={classes!("popup")}>
                    {
                        match expand_gossip(
                            &send,
                            &receive,
                            *size,
                            *branching,
                            *cluster_coeff,
                            disjoint_names,
                        ) {
                            Ok(delta_q) => html! { <DeltaQComponent delta_q={delta_q.arc()} on_change={|_| {}} /> },
                            Err(e) => html! { <div>{e.to_string()}</div> },
                        }
                    }
                </div>
            }
        </div>
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct MinProps {
    pub outcomes: Arc<[Outcome]>,
    pub label: &'static str,
    pub on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(Min)]
pub fn min(props: &MinProps) -> Html {
    html! {
        <div class={classes!("row", "frame")}>
            <div class={classes!("row", "center")}>{props.label}</div>
            <div class={classes!("column", "left")} style="border-left: 2px solid black;">
                { for props.outcomes.iter().map(|outcome| html! {
                    <div class={classes!("row", "left")} >
                        <DeltaQComponent delta_q={Arc::new(DeltaQExpr::Outcome(outcome.clone()))} on_change={|_| {}} />
                    </div>
                }) }
            </div>
        </div>
    }
}
