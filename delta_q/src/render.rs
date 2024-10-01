use crate::{delta_q::DeltaQ, EvaluationContext, CDF};
use charts_rs::{Axis, Canvas, Color, Point, Polyline};
use iter_tools::Itertools;
use std::{rc::Rc, sync::Arc};
use web_sys::HtmlInputElement;
use yew::{prelude::*, virtual_dom::VNode};

/// A piece of context that tells the DeltaQ rendering components to which named expression they belong.
#[derive(Clone, PartialEq)]
pub struct DeltaQContext {
    pub eval_ctx: Rc<EvaluationContext>,
    pub name: String,
}

impl DeltaQContext {
    pub fn new(eval_ctx: &EvaluationContext, name: &str) -> Self {
        Self {
            eval_ctx: Rc::new(eval_ctx.clone()),
            name: name.to_owned(),
        }
    }
}

#[derive(Properties, Clone, PartialEq, Debug)]
pub struct Props {
    pub delta_q: DeltaQ,
    pub on_change: Callback<(String, Option<DeltaQ>)>,
}

#[function_component(DeltaQComponent)]
pub fn delta_q_component(props: &Props) -> Html {
    // web_sys::console::log_1(&wasm_bindgen::JsValue::from_str(&format!("{props:?}")));
    let on_change = props.on_change.clone();
    match &props.delta_q {
        DeltaQ::BlackBox => {
            html! { <BlackBox {on_change} /> }
        }
        DeltaQ::Name(name, rec) => {
            html! { <NameComponent name={(&**name).to_owned()} rec={*rec} {on_change} /> }
        }
        DeltaQ::CDF(cdf) => {
            html! { <div class={classes!("cdf")}>{ format!("{}", cdf) }</div> }
        }
        DeltaQ::Seq(first, second) => {
            html!(<Seq first={(**first).clone()} second={(**second).clone()} {on_change} />)
        }
        DeltaQ::Choice(first, first_weight, second, second_weight) => {
            html!(<Branch top={(**first).clone()} bottom={(**second).clone()} {on_change} kind={BranchKind::Choice(*first_weight, *second_weight)} />)
        }
        DeltaQ::ForAll(first, second) => {
            html!(<Branch top={(**first).clone()} bottom={(**second).clone()} kind={BranchKind::ForAll} {on_change} />)
        }
        DeltaQ::ForSome(first, second) => {
            html!(<Branch top={(**first).clone()} bottom={(**second).clone()} kind={BranchKind::ForSome} {on_change} />)
        }
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct BlackBoxProps {
    pub on_change: Callback<(String, Option<DeltaQ>)>,
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
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&name))));
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
    pub on_change: Callback<(String, Option<DeltaQ>)>,
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
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name_rec(&new_name, rec))));
        }
    ));

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
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::seq(DeltaQ::name(&name), DeltaQ::BlackBox))))) }>{ "append" }</button>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(DeltaQ::name(&name), 1.0, DeltaQ::BlackBox, 1.0))))) }>{ "make choice" }</button>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_all(DeltaQ::name(&name), DeltaQ::BlackBox))))) }>{ "make forAll" }</button>
                    <button onclick={cloned!(on_change, name, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_some(DeltaQ::name(&name), DeltaQ::BlackBox))))) }>{ "make forSome" }</button>
                    <button onclick={cloned!(on_change, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::BlackBox))))}>{ "black box" }</button>
                    <button onclick={cloned!(on_change, ctx, popup, name;
                        move |_| { popup.set(false); if let Some(dq) = ctx.eval_ctx.get(&name) { on_change.emit((ctx.name.clone(), Some(dq.clone()))) } })}>{ "inline" }</button>
                </div>
            }
        </div>
    }
}

#[derive(Properties, Clone, PartialEq)]
pub struct SeqProps {
    pub first: DeltaQ,
    pub second: DeltaQ,
    pub on_change: Callback<(String, Option<DeltaQ>)>,
}

#[function_component(Seq)]
pub fn seq(props: &SeqProps) -> Html {
    let on_change = props.on_change.clone();
    let first = props.first.clone();
    let second = props.second.clone();
    let ctx = use_context::<DeltaQContext>().unwrap();

    let on_first_change = Callback::from(cloned!(second, on_change, ctx;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(DeltaQ::seq(delta_q, second.clone()))));
            }
        }
    ));

    let on_second_change = Callback::from(cloned!(first, on_change, ctx;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(DeltaQ::seq(first.clone(), delta_q))));
            }
        }
    ));

    let popup = use_state(|| false);
    let name = use_state(|| "".to_string());
    let oninput = Callback::from(cloned!(name; move |e: InputEvent| {
        name.set(e.target_unchecked_into::<HtmlInputElement>().value());
    }));
    let onsubmit = Callback::from(cloned!(name, on_change, ctx, first, second;
        move |e: SubmitEvent| {
            e.prevent_default();
            on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&name))));
            on_change.emit(((*name).clone(), Some(DeltaQ::seq(first.clone(), second.clone()))));
        }
    ));

    html! {
        <div class={classes!("row", "center", "frame")}>
            <DeltaQComponent delta_q={first.clone()} on_change={on_first_change} />
            <div class={classes!("seqSymbol", "anchor")} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
                if *popup {
                    <div class={classes!("popup")}>
                    <button onclick={cloned!(popup;
                        move |_| popup.set(false))}> { "abort" } </button>
                    <button onclick={cloned!(on_change, first, second, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(DeltaQ::seq(first.clone(), second.clone()), 1.0, DeltaQ::BlackBox, 1.0)))))}> { "make choice" } </button>
                    <button onclick={cloned!(on_change, first, second, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_all(DeltaQ::seq(first.clone(), second.clone()), DeltaQ::BlackBox)))))}> { "make forAll" } </button>
                    <button onclick={cloned!(on_change, first, second, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::for_some(DeltaQ::seq(first.clone(), second.clone()), DeltaQ::BlackBox)))))}> { "make forSome" } </button>
                    <button onclick={cloned!(on_change, first, second, popup, ctx;
                        move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(DeltaQ::seq(second.clone(), first.clone())))) })}>{ "switch" }</button>
                    <button onclick={cloned!(popup, on_change, first, ctx;
                        move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(first.clone()))) })}>{ "keep left" }</button>
                    <button onclick={cloned!(popup, on_change, second, ctx;
                        move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(second.clone()))) })}>{ "keep right" }</button>
                    <button onclick={cloned!(on_change, ctx;
                        move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::BlackBox))))}>{ "black box" }</button>
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
    pub top: DeltaQ,
    pub bottom: DeltaQ,
    pub on_change: Callback<(String, Option<DeltaQ>)>,
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
    let kind = match &props.kind {
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
    let top_input = Callback::from(cloned!(top_frac;
        move |e: InputEvent| top_frac.set(e.target_unchecked_into::<HtmlInputElement>().value_as_number() as f32)));
    let bottom_input = Callback::from(cloned!(bottom_frac;
        move |e: InputEvent| bottom_frac.set(e.target_unchecked_into::<HtmlInputElement>().value_as_number() as f32)));
    let frac_submit = Callback::from(
        cloned!(popup, on_change, top, bottom, top_frac, bottom_frac, ctx;
        move |e: SubmitEvent| {
            e.prevent_default();
            popup.set(false);
            on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(top.clone(), *top_frac, bottom.clone(), *bottom_frac))));
        }),
    );

    let abstract_name = use_state(|| "".to_string());
    let abstract_input = Callback::from(cloned!(abstract_name;
        move |e: InputEvent| abstract_name.set(e.target_unchecked_into::<HtmlInputElement>().value())));
    let abstract_submit = Callback::from(
        cloned!(abstract_name, on_change, ctx, bottom, bottom_frac, top, top_frac;
            move |e: SubmitEvent| {
                e.prevent_default();
                on_change.emit((ctx.name.clone(), Some(DeltaQ::name(&abstract_name))));
                on_change.emit(((*abstract_name).clone(), Some(DeltaQ::choice(top.clone(), *top_frac, bottom.clone(), *bottom_frac))));
            }
        ),
    );

    html!(
    <div class={classes!("row", "center", "branchKind", "anchor")} onclick={cloned!(popup; move |_| if !*popup { popup.set(true) })}>
        { kind }
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
                    on_change.emit((ctx.name.clone(), Some(DeltaQ::for_all(top.clone(), bottom.clone()))))
                })}>{ "make forAll" }</button>
                <button onclick={cloned!(popup, on_change, top, bottom, ctx; move |_| {
                    popup.set(false);
                    on_change.emit((ctx.name.clone(), Some(DeltaQ::for_some(top.clone(), bottom.clone()))))
                })}>{ "make forSome" }</button>
                <button onclick={cloned!(popup, on_change, top, bottom, ctx; move |_| {
                    popup.set(false);
                    on_change.emit((ctx.name.clone(), Some(DeltaQ::choice(bottom.clone(), *bottom_frac, top.clone(), *top_frac))))
                })}>{ "switch" }</button>
                <button onclick={cloned!(popup, on_change, top, ctx;
                    move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(top.clone()))) })}>{ "keep top" }</button>
                <button onclick={cloned!(popup, on_change, bottom, ctx;
                    move |_| { popup.set(false); on_change.emit((ctx.name.clone(), Some(bottom.clone()))) })}>{ "keep bottom" }</button>
                <button onclick={cloned!(on_change, ctx;
                    move |_| on_change.emit((ctx.name.clone(), Some(DeltaQ::BlackBox))))}>{ "black box" }</button>
                <form onsubmit={abstract_submit}>
                    <input type="submit" value="abstract" />
                    <input type="text" value={(*abstract_name).clone()} oninput={abstract_input} />
                </form>
            </div>
        }
    </div>)
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
    let constructor: Arc<dyn Fn(Arc<DeltaQ>, Arc<DeltaQ>) -> DeltaQ> = match kind {
        BranchKind::Choice(l, r) => Arc::new(move |dql, dqr| DeltaQ::Choice(dql, l, dqr, r)),
        BranchKind::ForAll => Arc::new(DeltaQ::ForAll),
        BranchKind::ForSome => Arc::new(DeltaQ::ForSome),
    };
    let ctx = use_context::<DeltaQContext>().unwrap();

    let on_top_change = Callback::from(cloned!(bottom, on_change, constructor, ctx;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(constructor(Arc::new(delta_q), Arc::new(bottom.clone())))));
            }
        }
    ));

    let on_bottom_change = Callback::from(cloned!(top, on_change, ctx;
        move |(name, delta_q)| {
            // if the name matches our context, edit the DeltaQ; otherwise just bubble up
            if name != ctx.name {
                on_change.emit((name, delta_q));
            } else if let Some(delta_q) = delta_q {
                on_change.emit((name, Some(constructor(Arc::new(top.clone()), Arc::new(delta_q)))));
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

pub fn cdf_to_svg(cdf: &CDF) -> Html {
    let mut canvas = Canvas::new(310.0, 110.0);
    let x_scale = 300.0 / cdf.width();
    canvas.polyline(Polyline {
        color: Some(Color::black()),
        stroke_width: 1.0,
        points: cdf
            .iter()
            .tuple_windows()
            .flat_map(|((x, y), (x2, _))| {
                vec![
                    Point {
                        x: x * x_scale + 10.0,
                        y: (1.0 - y) * 100.0 + 1.0,
                    },
                    Point {
                        x: x2 * x_scale + 10.0,
                        y: (1.0 - y) * 100.0 + 1.0,
                    },
                ]
            })
            .collect(),
    });
    canvas.axis(Axis {
        stroke_color: Some(Color::black()),
        left: 10.0,
        top: 101.0,
        width: 300.0,
        split_number: 300,
        tick_interval: x_scale as usize,
        ..Default::default()
    });
    canvas.axis(Axis {
        stroke_color: Some(Color::black()),
        position: charts_rs::Position::Left,
        top: 1.0,
        left: 10.0,
        height: 100.0,
        split_number: 1,
        ..Default::default()
    });
    let svg = VNode::from_html_unchecked(canvas.svg().unwrap().into());
    html! {
        <>
            <p class={classes!("result")}>{ "result: " }{cdf.to_string()} </p>
            { svg }
        </>
    }
}

impl Reducible for EvaluationContext {
    type Action = (String, Option<DeltaQ>);

    fn reduce(self: Rc<Self>, (name, dq): Self::Action) -> Rc<Self> {
        let mut ctx = (*self).clone();
        if let Some(dq) = dq {
            ctx.put(name, dq);
        } else {
            ctx.remove(&name);
        }
        Rc::new(ctx)
    }
}
