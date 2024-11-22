macro_rules! cloned {
    ($($name:ident),*; $e:expr) => {{
        $(let $name = $name.clone();)*
        $e
    }};
}

use delta_q::{
    CalcCdf, DeltaQComponent, DeltaQContext, DeltaQExpr, EphemeralContext, EvalCtxAction,
    PersistentContext, StepFunction, CDF,
};
use gloo_utils::window;
use js_sys::Reflect;
use std::{str::FromStr, sync::Arc};
use wasm_bindgen::{prelude::Closure, JsCast, JsValue};
use web_sys::{HtmlElement, HtmlInputElement, HtmlTextAreaElement, MessageEvent, MessageEventInit};
use yew::{prelude::*, suspense::use_future_with};
use yew_agent::{oneshot::OneshotProvider, prelude::use_oneshot_runner};
use yew_hooks::use_local_storage;

#[function_component(AppMain)]
fn app_main() -> HtmlResult {
    let ctx_handle = use_local_storage::<PersistentContext>("delta_q".to_owned());
    let ctx = use_reducer(cloned!(ctx_handle; move || (*ctx_handle).clone().unwrap_or_default()));
    if Some(&*ctx) != ctx_handle.as_ref() {
        ctx_handle.set((*ctx).clone());
    }

    // epoch counter to trigger recomputation when the context changes
    let epoch = use_state(|| 0);

    let ctx_popup = use_state(|| false);
    let ctx_text = use_state(|| String::new());
    let ctx_text_status = use_state(|| "OK".to_owned());
    let ctx_text_ref = use_node_ref();

    let ctx_text_input = Callback::from(cloned!(ctx_text, ctx_text_status; move |e: InputEvent| {
        let text = e.target_unchecked_into::<HtmlInputElement>().value();
        match text.parse::<PersistentContext>() {
            Ok(_) => ctx_text_status.set("OK".to_owned()),
            Err(e) => ctx_text_status.set(e),
        }
        ctx_text.set(text);
    }));
    let ctx_popup_show = Callback::from(cloned!(ctx_popup, ctx_text, ctx; move |_: MouseEvent| {
        ctx_popup.set(true);
        ctx_text.set(ctx.to_string());
    }));
    use_effect_with(
        ctx_popup.clone(),
        cloned!(ctx_text_ref, ctx_text, ctx_popup; move |popup| {
            if **popup {
                let Some(textarea) = ctx_text_ref.cast::<HtmlTextAreaElement>() else {
                    return;
                };
                textarea.focus().expect("focus failed");
                textarea.set_value(&*ctx_text);
                let escape = Closure::<dyn Fn(KeyboardEvent)>::new(move |e: KeyboardEvent| if e.key() == "Escape" {
                    ctx_popup.set(false)
                }).into_js_value();
                textarea.add_event_listener_with_callback("keydown", escape.unchecked_ref()).expect("listening on keydown failed");
            }
        }),
    );
    let ctx_popup_close =
        Callback::from(cloned!(ctx_popup, ctx_text, epoch, ctx; move |save: bool| {
            ctx_popup.set(false);
            if !save {
                return;
            }
            if let Ok(cx) = PersistentContext::from_str(&*ctx_text) {
                ctx.dispatch(EvalCtxAction::Set(cx));
                epoch.set(*epoch + 1);
            }
        }));

    let selected = use_state::<Option<String>, _>(|| None);
    let select = cloned!(selected; Callback::from(move |n| selected.set(Some(n))));

    let agent_status = use_state(|| "".to_owned());
    let agent = use_oneshot_runner::<CalcCdf>();
    use_future_with(
        (selected.clone(), epoch.clone()),
        cloned!(agent_status, ctx; move |deps| async move {
            if let Some(name) = deps.0.as_deref() {
                let cdf = match agent.run((name.to_string(), (*ctx).clone())).await {
                    Ok(cdf) => cdf,
                    Err(e) => {
                        let init = MessageEventInit::new();
                        init.set_data(&wasm_bindgen::JsValue::null());
                        let _ = window().dispatch_event(&*MessageEvent::new_with_event_init_dict("rootjs", &init).unwrap());
                                agent_status.set(format!("evaluation error: {e}"));
                        return;
                    }
                };
                let data = mk_graph_obj(name, &cdf.cdf.steps().map(|x| CDF::from_step_at(*x)));
                Reflect::set(&data, &"loads".into(), &cdf.load.iter().map(|(metric, steps)| mk_graph_obj(metric, steps)).collect::<js_sys::Array>()).unwrap();
                let init = MessageEventInit::new();
                init.set_data(&data);
                let _ = window().dispatch_event(&*MessageEvent::new_with_event_init_dict("rootjs", &init).unwrap());
                agent_status.set("OK".to_owned());
            }
        }),
    )?;

    let on_change = cloned!(ctx, epoch;
        Callback::from(move |(name, dq): (String, Option<Arc<DeltaQExpr>>)| {
            if let Some(dq) = dq {
                ctx.dispatch(EvalCtxAction::Put(name.clone(), dq.into()));
            } else {
                ctx.dispatch(EvalCtxAction::Remove(name));
            }
            epoch.set(*epoch + 1);
        })
    );

    let focused_constraint = use_state(|| Option::<HtmlInputElement>::None);
    use_effect(cloned!(focused_constraint; move || {
        if let Some(focused) = focused_constraint.as_ref() {
            focused.focus().expect("focus failed");
            let escape = Closure::<dyn Fn(KeyboardEvent)>::new(cloned!(focused_constraint; move |e: KeyboardEvent| if e.key() == "Escape" {
                focused_constraint.set(None)
            })).into_js_value();
            focused.add_event_listener_with_callback("keydown", escape.unchecked_ref()).expect("listening on keydown failed");
        }
    }));
    let toggle_constraint = cloned!(ctx, epoch; Callback::from(move |name: smallstr::SmallString<[u8; 16]>| {
        ctx.dispatch(EvalCtxAction::ToggleConstraint(name));
        epoch.set(*epoch + 1);
    }));
    let edit_constraint = cloned!(ctx; Callback::from(move |(name, event): (smallstr::SmallString<[u8; 16]>, InputEvent)| {
        let value = event.target_unchecked_into::<HtmlInputElement>().value();
        ctx.dispatch(EvalCtxAction::EditConstraint(name, value));
        epoch.set(*epoch + 1);
    }));

    let mut sel_found = false;
    let mut cache = EphemeralContext::default();
    let list_items = ctx
        .iter()
        .map(|(k, v)| {
            let name = k.clone();
            let constraint = ctx.constraint(&name);
            let check = (|| {
                let c = ctx.get(&constraint?)?;
                let c = c.eval(&ctx, &mut cache).ok()?;
                let n = ctx.get(&name)?;
                let n = n.eval(&ctx, &mut cache).ok()?;
                Some(n.cdf >= c.cdf)
            })();
            let check = match check {
                Some(true) => "slack",
                Some(false) => "danger",
                None => "failed",
            };
            let select = select.clone();
            let sel = if selected.as_deref() == Some(k.as_str()) {
                sel_found = true;
                Some("selected")
            } else {
                None
            };
            html! {
                <li class={classes!("row")}>
                    <button onclick={cloned!(name, on_change; move |_| on_change.emit((name.to_string(), None)))}>{ "delete "}</button>
                    <button onclick={cloned!(toggle_constraint, name; move |_| toggle_constraint.emit(name.clone()))}>{ "constraint" }</button>
                    if let Some(c) = constraint {
                        <input type="text" value={c.to_string()} class={classes!(check)} oninput={edit_constraint.reform(cloned!(name; move |e| (name.clone(), e)))}
                            onfocus={cloned!(focused_constraint; move |e: FocusEvent| focused_constraint.set(Some(e.target_unchecked_into::<HtmlInputElement>())))}
                        />
                    }
                    <div class={classes!("expression", sel)} style="margin-left: 8px;" onclick={select.reform(move |_| name.to_string())}>
                        { k }{ ": " }<EditExpression name={k.to_string()} value={v.arc()} on_change={on_change.clone()} selected={sel.is_some()} />
                    </div>
                </li>
            }
        })
        .collect::<Html>();
    if selected.is_some() && !sel_found {
        selected.set(None);
        // this only takes effect on the next render!
    }

    let list = use_node_ref();
    let scroll = use_state(|| 0);
    use_effect(cloned!(scroll, list; move || {
        if let Some(list) = list.cast::<HtmlElement>() {
            list.set_scroll_top(*scroll);
        }
    }));

    let dq = selected.as_ref().and_then(|name| ctx.get(name));
    // web_sys::console::log_1(&JsValue::from_str(&format!("{dq:?}")));

    let add_on_change = on_change.reform(
        cloned!(selected; move |x: (String, Option<Arc<DeltaQExpr>>)| {
            selected.set(Some(x.0.clone()));
            x
        }),
    );

    Ok(html! {
    <div>
        <p>{ "context:" }<button onclick={ctx_popup_show}>{ "edit" }</button></p>
        <ul class={classes!("ctx_list")} ref={list} onscroll={cloned!(scroll; move |e: Event| scroll.set(e.target_unchecked_into::<HtmlElement>().scroll_top()))}>
        { list_items }
        </ul>
        <AddExpression on_change={add_on_change} />
        if let (Some(name), Some(dq)) = (selected.as_ref(), dq) {
            <p>{ "selected: " } { name }</p>
            <div style="background-color: #f0f0f0; padding: 4px; margin: 4px; display: flex; flex-direction: row;">
                <ContextProvider<DeltaQContext> context={DeltaQContext::new(&ctx, &name)}>
                    <DeltaQComponent delta_q={dq.arc()} {on_change} />
                </ContextProvider<DeltaQContext>>
            </div>
        }
        <p>{ "agent status: " }{ &*agent_status }</p>
        if *ctx_popup {
            <div class={classes!("ctx_popup")}>
                <p>
                    <button onclick={cloned!(ctx_popup_close; move |_| ctx_popup_close.emit(true))} disabled={&*ctx_text_status != "OK"} >{ "save" }</button>
                    <button onclick={cloned!(ctx_popup_close; move |_| ctx_popup_close.emit(false))} >{ "cancel" }</button>
                </p>
                <textarea oninput={ctx_text_input} rows={(ctx_text.lines().count() + 1).to_string()} cols="80" ref={ctx_text_ref} />
                <pre>{ &*ctx_text_status }</pre>
            </div>
        }
    </div>
    })
}

fn mk_graph_obj(name: &str, steps: &StepFunction<CDF>) -> js_sys::Object {
    let data = js_sys::Object::new();
    Reflect::set(
        &data,
        &"bins".into(),
        &steps
            .graph_iter()
            .map(|x| JsValue::from(x.0))
            .collect::<js_sys::Array>(),
    )
    .unwrap();
    Reflect::set(
        &data,
        &"values".into(),
        &steps
            .graph_iter()
            .map(|x| {
                x.1.graph_iter()
                    .map(|(x, y)| {
                        [x, y]
                            .iter()
                            .map(|z| JsValue::from(*z))
                            .collect::<js_sys::Array>()
                    })
                    .collect::<js_sys::Array>()
            })
            .collect::<js_sys::Array>(),
    )
    .unwrap();
    Reflect::set(&data, &"max".into(), &(steps.max_x() * 1.2).max(0.1).into()).unwrap();
    Reflect::set(&data, &"name".into(), &name.into()).unwrap();
    data
}

#[derive(Properties, PartialEq, Clone)]
struct AddExpressionProps {
    on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(AddExpression)]
fn add_expression(props: &AddExpressionProps) -> HtmlResult {
    let name = use_state(|| "".to_owned());
    let value = (*name).clone();
    let on_change = props.on_change.clone();
    let on_submit = cloned!(name, on_change; Callback::from(move |e: SubmitEvent| {
        e.prevent_default();
        name.set("".to_owned());
        on_change.emit(((*name).clone(), Some(DeltaQExpr::BlackBox.into())));
    }));
    let on_input = Callback::from(move |e: InputEvent| {
        name.set(e.target_unchecked_into::<HtmlInputElement>().value())
    });

    Ok(html! {
        <form onsubmit={on_submit}>
            <button type="submit">{ "add" }</button>
            <input type="text" {value} oninput={on_input} />
        </form>
    })
}

#[derive(Properties, PartialEq, Clone, Debug)]
struct EditExpressionProps {
    name: String,
    value: Arc<DeltaQExpr>,
    selected: bool,
    on_change: Callback<(String, Option<Arc<DeltaQExpr>>)>,
}

#[function_component(EditExpression)]
fn edit_expression(props: &EditExpressionProps) -> HtmlResult {
    let name = props.name.clone();
    let orig = props.value.clone();
    let on_change = props.on_change.clone();

    let editing = use_state(|| false);
    let buffer = use_state(|| props.value.to_string());
    let result = use_state(|| "OK".to_owned());

    let value = use_state(|| props.value.clone());
    let on_submit = cloned!(name, value, on_change, editing; Callback::from(move |e: SubmitEvent| {
        e.prevent_default();
        editing.set(false);
        on_change.emit((name.clone(), Some((*value).clone())));
    }));
    let on_input = cloned!(buffer, value, result; Callback::from(move |e: InputEvent| {
        let v = e.target_unchecked_into::<HtmlInputElement>().value();
        buffer.set(v.clone());
        match v.parse::<DeltaQExpr>() {
            Ok(dq) => {
                value.set(dq.into());
                result.set("OK".to_owned());
            }
            Err(e) => {
                result.set(e);
            }
        }
    }));

    use_memo(
        (props.value.clone(), props.selected),
        cloned!(editing, value, buffer; move |x| {
               editing.set(false);
               value.set(x.0.clone());
               buffer.set(x.0.to_string());
            }
        ),
    );

    let field = use_node_ref();
    use_effect_with(
        editing.clone(),
        cloned!(field, buffer; move |editing| {
            if **editing {
                let Some(field) = field.cast::<HtmlInputElement>() else {
                    return;
                };
                field.focus().expect("focus failed");
                let escape = Closure::<dyn Fn(KeyboardEvent)>::new(cloned!(editing; move |e: KeyboardEvent| if e.key() == "Escape" {
                    editing.set(false)
                })).into_js_value();
                field.add_event_listener_with_callback("keydown", escape.unchecked_ref()).expect("listening on keydown failed");
                buffer.set(orig.to_string());
            }
        }),
    );

    Ok(html! {
        if *editing {
            <div class={classes!("dq_edit")}>
                <form onsubmit={on_submit}>
                    <input type="submit" value="update" />
                    <input type="text" value={(*buffer).clone()} oninput={on_input} ref={field} />
                </form>
                <pre>{ &*result }</pre>
            </div>
        } else {
            <span class={classes!("dq_show")} onclick={cloned!(editing; move |_| editing.set(true))}>{ value.to_string() }</span>
        }
    })
}

#[function_component(App)]
fn app() -> Html {
    let waiting = html! { <p>{ "Waiting for DeltaQ..." }</p> };

    html! {
        <div>
            <h1>{ "DeltaQ Editor" }</h1>
            <div style="display: flex; flex-direction: row; height: 40%;">
                <div id="output" style="width: 50%; height: 100%; border: 1px solid black;" />
                <div id="loads" style="width: 50%; height: 100%; border: 1px solid black;" />
            </div>
            <Suspense fallback={waiting}>
                <OneshotProvider<CalcCdf> path="worker.js">
                    <AppMain />
                </OneshotProvider<CalcCdf>>
            </Suspense>
        </div>
    }
}

fn main() {
    yew::Renderer::<App>::new().render();
}
