use axum::{Router, extract::Path, http::StatusCode, response::IntoResponse};
use clap::Parser;
use hyper_util::rt::TokioIo;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tower::Service;

#[derive(Parser)]
#[command(name = "axum-fileserver")]
struct Args {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,
    #[arg(long, default_value_t = 8080)]
    port: u16,
    #[arg(long, default_value = "./public")]
    root: String,
    #[arg(long, default_value_t = false)]
    nofs: bool,
}

#[derive(Clone)]
struct St {
    root: String,
    cache: Option<Arc<HashMap<String, Vec<u8>>>>,
}

fn content_type(p: &str) -> &'static str {
    if p.ends_with(".html") {
        "text/html"
    } else if p.ends_with(".json") {
        "application/json"
    } else {
        "application/octet-stream"
    }
}

async fn serve_file(
    axum::extract::State(st): axum::extract::State<St>,
    path: Option<Path<String>>,
) -> impl IntoResponse {
    let rel = match &path {
        Some(Path(p)) => p.clone(),
        None => "index.html".to_string(),
    };
    if let Some(cache) = &st.cache {
        return match cache.get(&rel) {
            Some(data) => (
                StatusCode::OK,
                [(axum::http::header::CONTENT_TYPE, content_type(&rel))],
                data.clone(),
            )
                .into_response(),
            None => StatusCode::NOT_FOUND.into_response(),
        };
    }
    let file_path = format!("{}/{}", st.root, rel);
    match lion::fs::read(&file_path).await {
        Ok(data) => (
            StatusCode::OK,
            [(axum::http::header::CONTENT_TYPE, content_type(&file_path))],
            data,
        )
            .into_response(),
        Err(_) => StatusCode::NOT_FOUND.into_response(),
    }
}

fn preload(root: &str) -> Arc<HashMap<String, Vec<u8>>> {
    let mut m = HashMap::new();
    for sub in ["small", "large"] {
        let dir = format!("{root}/{sub}");
        if let Ok(rd) = std::fs::read_dir(&dir) {
            for e in rd.flatten() {
                if let Ok(data) = std::fs::read(e.path()) {
                    m.insert(format!("{sub}/{}", e.file_name().to_string_lossy()), data);
                }
            }
        }
    }
    Arc::new(m)
}

fn main() {
    let args = Args::parse();
    tracing_subscriber::fmt::init();

    let cache = if args.nofs { Some(preload(&args.root)) } else { None };
    let st = St { root: args.root.clone(), cache };

    let rt = lion::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    rt.block_on(async move {
        let app = Router::new()
            .route("/", axum::routing::get(serve_file))
            .route("/{*path}", axum::routing::get(serve_file))
            .with_state(st);

        let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
        let listener = lion::net::TcpListener::bind(addr).await.unwrap();

        loop {
            let (stream, _) = listener.accept().await.unwrap();
            let tower_service = app.clone();

            lion::spawn(async move {
                let stream = TokioIo::new(stream);
                let hyper_service = hyper::service::service_fn(move |req| {
                    let mut svc = tower_service.clone();
                    async move { svc.call(req).await }
                });

                if let Err(err) = hyper_util::server::conn::auto::Builder::new(LocalExec)
                    .serve_connection(stream, hyper_service)
                    .await
                {
                    tracing::error!("connection error: {}", err);
                }
            });
        }
    });
}

#[derive(Clone)]
struct LocalExec;

impl<F> hyper::rt::Executor<F> for LocalExec
where
    F: std::future::Future + Send + 'static,
    F::Output: Send + 'static,
{
    fn execute(&self, fut: F) {
        lion::spawn(fut);
    }
}
