use actix_web::{delete, get, put, web, App, HttpRequest, HttpResponse, HttpServer, Responder};
use delta_q::{DeltaQ, EvaluationContext, CDF};
use include_dir::{include_dir, Dir};
use parking_lot::Mutex;
use std::io;
use tracing_subscriber::EnvFilter;

static ASSETS: Dir = include_dir!("$CARGO_MANIFEST_DIR/dist");

struct Data {
    ctx: Mutex<EvaluationContext>,
}

#[get("/")]
async fn index() -> impl Responder {
    tracing::info!("GET /");
    HttpResponse::Ok().content_type("text/html").body(
        ASSETS
            .get_file("index.html")
            .expect("no index.html in dist/")
            .contents(),
    )
}

async fn assets(req: HttpRequest) -> impl Responder {
    tracing::info!("GET {}", req.path());
    let path = &req.path()[1..];
    let mime = if let Some(pos) = path.rfind('.') {
        match &path[pos + 1..] {
            "html" => "text/html",
            "js" => "application/javascript",
            "css" => "text/css",
            "wasm" => "application/wasm",
            "txt" => "text/plain",
            _ => "application/octet-stream",
        }
    } else {
        "application/octet-stream"
    };
    Ok::<HttpResponse, io::Error>(
        HttpResponse::Ok().content_type(mime).body(
            ASSETS
                .get_file(path)
                .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "not found"))?
                .contents(),
        ),
    )
}

#[get("/delta_q")]
async fn all_delta_q(data: web::Data<Data>) -> impl Responder {
    tracing::info!("GET /delta_q");
    HttpResponse::Ok()
        .insert_header(("Cache-Control", "no-store"))
        .json(&*data.ctx.lock())
}

#[get("/delta_q/{name}")]
async fn get_delta_q(data: web::Data<Data>, name: web::Path<String>) -> impl Responder {
    tracing::info!("GET /delta_q/{}", name);
    let mut ctx = data.ctx.lock();
    match ctx.eval(&name) {
        Ok(dq) => HttpResponse::Ok()
            .insert_header(("Cache-Control", "no-store"))
            .json(dq),
        Err(e) => HttpResponse::NotFound()
            .insert_header(("Cache-Control", "no-store"))
            .body(e.to_string()),
    }
}

#[put("/delta_q/{name}")]
async fn put_delta_q(
    data: web::Data<Data>,
    name: web::Path<String>,
    dq: web::Json<DeltaQ>,
) -> impl Responder {
    tracing::info!("PUT /delta_q/{}", name);
    let mut ctx = data.ctx.lock();
    ctx.put(name.into_inner(), dq.into_inner());
    HttpResponse::Ok().finish()
}

#[delete("/delta_q/{name}")]
async fn delete_delta_q(data: web::Data<Data>, name: web::Path<String>) -> impl Responder {
    tracing::info!("DELETE /delta_q/{}", name);
    let mut ctx = data.ctx.lock();
    if ctx.remove(&name).is_some() {
        HttpResponse::Ok().finish()
    } else {
        HttpResponse::NotFound().finish()
    }
}

#[actix_web::main]
async fn main() -> io::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    let data = web::Data::new(Data {
        ctx: Mutex::new(EvaluationContext::default()),
    });

    // add two delta_q to the context
    let mut ctx = data.ctx.lock();
    ctx.put("black".to_owned(), DeltaQ::BlackBox);
    ctx.put(
        "cdf".to_owned(),
        DeltaQ::cdf(CDF::step(&[(0.1, 0.33), (0.2, 0.66), (0.4, 1.0)]).unwrap()),
    );
    ctx.put(
        "out".to_owned(),
        DeltaQ::seq(
            DeltaQ::name("cdf"),
            DeltaQ::choice(
                DeltaQ::name("cdf"),
                0.5,
                DeltaQ::for_all(
                    DeltaQ::name("cdf"),
                    DeltaQ::seq(DeltaQ::name("cdf"), DeltaQ::name("cdf")),
                ),
                3.0,
            ),
        ),
    );
    drop(ctx);

    let server = HttpServer::new(move || {
        App::new()
            .app_data(data.clone())
            .service(index)
            .service(all_delta_q)
            .service(get_delta_q)
            .service(put_delta_q)
            .service(delete_delta_q)
            .route("/{f:.*}", web::get().to(assets))
    })
    .workers(1);
    println!("Listening on http://localhost:8080");
    server.bind(("localhost", 8080))?.run().await
}
