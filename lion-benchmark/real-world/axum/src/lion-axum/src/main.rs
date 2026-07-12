use axum::{Router, extract::Path, http::StatusCode, response::IntoResponse};
use clap::Parser;
use hyper_util::rt::TokioIo;
use std::net::SocketAddr;
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
}

async fn serve_file(
    axum::extract::State(root): axum::extract::State<String>,
    path: Option<Path<String>>,
) -> impl IntoResponse {
    let file_path = match &path {
        Some(Path(p)) => format!("{}/{}", root, p),
        None => format!("{}/index.html", root),
    };

    match lion::fs::read(&file_path).await {
        Ok(data) => {
            let content_type = if file_path.ends_with(".html") {
                "text/html"
            } else if file_path.ends_with(".json") {
                "application/json"
            } else {
                "application/octet-stream"
            };
            (
                StatusCode::OK,
                [(axum::http::header::CONTENT_TYPE, content_type)],
                data,
            )
                .into_response()
        }
        Err(_) => StatusCode::NOT_FOUND.into_response(),
    }
}

fn main() {
    let args = Args::parse();

    tracing_subscriber::fmt::init();

    let rt = lion::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    rt.block_on(async {
        let app = Router::new()
            .route("/", axum::routing::get(serve_file))
            .route("/{*path}", axum::routing::get(serve_file))
            .with_state(args.root.clone());

        let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
        tracing::info!("serving {} on {}", args.root, addr);

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

                if let Err(err) = hyper_util::server::conn::auto::Builder::new(TokioExecutor)
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
struct TokioExecutor;

impl<F> hyper::rt::Executor<F> for TokioExecutor
where
    F: std::future::Future + Send + 'static,
    F::Output: Send + 'static,
{
    fn execute(&self, fut: F) {
        lion::spawn(fut);
    }
}
