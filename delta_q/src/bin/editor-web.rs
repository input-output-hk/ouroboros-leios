macro_rules! cloned {
    ($($name:ident),*; $e:expr) => {{
        $(let $name = $name.clone();)*
        $e
    }};
}

use delta_q::{CalcCdf, DeltaQ, DeltaQComponent, DeltaQContext, EvaluationContext};
use gloo_utils::window;
use js_sys::Reflect;
use wasm_bindgen::JsValue;
use web_sys::{HtmlInputElement, MessageEvent, MessageEventInit};
use yew::{prelude::*, suspense::use_future_with};
use yew_agent::{oneshot::OneshotProvider, prelude::use_oneshot_runner};
use yew_hooks::use_local_storage;

#[function_component(AppMain)]
fn app_main() -> HtmlResult {
    let ctx_handle = use_local_storage::<EvaluationContext>("delta_q".to_owned());
    let ctx = use_reducer(cloned!(ctx_handle; move || (*ctx_handle).clone().unwrap_or_default()));
    if Some(&*ctx) != ctx_handle.as_ref() {
        ctx_handle.set((*ctx).clone());
    }

    let selected = use_state::<Option<String>, _>(|| None);
    let select = cloned!(selected; Callback::from(move |n| selected.set(Some(n))));

    // epoch counter to trigger recomputation when the context changes
    let epoch = use_state(|| 0);

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
                let data = js_sys::Object::new();
                Reflect::set(&data, &"bins".into(), &cdf.iter().map(|x| JsValue::from(x.0)).collect::<js_sys::Array>()).unwrap();
                Reflect::set(&data, &"values".into(), &cdf.iter().map(|x| JsValue::from(x.1)).collect::<js_sys::Array>()).unwrap();
                Reflect::set(&data, &"max".into(), &(cdf.width() * 1.2).max(0.1).into()).unwrap();
                Reflect::set(&data, &"name".into(), &name.into()).unwrap();
                let init = MessageEventInit::new();
                init.set_data(&data);
                let _ = window().dispatch_event(&*MessageEvent::new_with_event_init_dict("rootjs", &init).unwrap());
                agent_status.set("OK".to_owned());
            }
        }),
    )?;

    let on_change = cloned!(ctx, epoch;
        Callback::from(move |(name, dq): (String, Option<DeltaQ>)| {
            ctx.dispatch((name.clone(), dq.clone()));
            epoch.set(*epoch + 1);
        })
    );

    let mut sel_found = false;
    let list_items = ctx
        .iter()
        .map(|(k, v)| {
            let name = k.clone();
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
                    <div class={classes!("expression", sel)} style="margin-left: 8px;" onclick={select.reform(move |_| name.to_string())}>
                        { k }{ ": " }<EditExpression name={k.to_string()} value={v.clone()} on_change={on_change.clone()} selected={sel.is_some()} />
                    </div>
                </li>
            }
        })
        .collect::<Html>();
    if selected.is_some() && !sel_found {
        selected.set(None);
        // this only takes effect on the next render!
    }

    let dq = selected.as_ref().and_then(|name| ctx.get(name));
    // web_sys::console::log_1(&JsValue::from_str(&format!("{dq:?}")));

    let add_on_change = on_change.reform(cloned!(selected; move |x: (String, Option<DeltaQ>)| {
        selected.set(Some(x.0.clone()));
        x
    }));

    Ok(html! {
    <div>
        <p>{ "context:" }</p>
        <ul>
        { list_items }
        </ul>
        <AddExpression on_change={add_on_change} />
        if let (Some(name), Some(dq)) = (selected.as_ref(), dq) {
            <p>{ "selected: " } { name }</p>
            <div style="background-color: #f0f0f0; padding: 4px; margin: 4px; display: flex; flex-direction: row;">
                <ContextProvider<DeltaQContext> context={DeltaQContext::new(&ctx, &name)}>
                    <DeltaQComponent delta_q={dq.clone()} {on_change} />
                </ContextProvider<DeltaQContext>>
            </div>
        }
        <p>{ "agent status: " }{ &*agent_status }</p>
    </div>
    })
}

#[derive(Properties, PartialEq, Clone)]
struct AddExpressionProps {
    on_change: Callback<(String, Option<DeltaQ>)>,
}

#[function_component(AddExpression)]
fn add_expression(props: &AddExpressionProps) -> HtmlResult {
    let name = use_state(|| "".to_owned());
    let value = (*name).clone();
    let on_change = props.on_change.clone();
    let on_submit = cloned!(name, on_change; Callback::from(move |e: SubmitEvent| {
        e.prevent_default();
        name.set("".to_owned());
        on_change.emit(((*name).clone(), Some(DeltaQ::BlackBox)));
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
    value: DeltaQ,
    selected: bool,
    on_change: Callback<(String, Option<DeltaQ>)>,
}

#[function_component(EditExpression)]
fn edit_expression(props: &EditExpressionProps) -> HtmlResult {
    let name = props.name.clone();
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
        match v.parse::<DeltaQ>() {
            Ok(dq) => {
                value.set(dq);
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
        cloned!(field; move |editing| {
            if **editing {
                let Some(field) = field.cast::<HtmlInputElement>() else {
                    return;
                };
                field.focus().expect("focus failed");
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
            <div id="output" style="width: 50%; height: 30%; border: 1px solid black;" />
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
