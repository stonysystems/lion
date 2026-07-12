#![cfg_attr(verus_keep_ghost, verus::trusted)]
// Filesystem utilities — unverified, moved verbatim from the unverified crate.
// Plain Rust over the executor blocking pool; trusted under Verus.
use std::path::{Path, PathBuf};
use lion_executor::spawn_blocking;
use lion_executor::JoinHandle;

pub async fn read_to_string(path: impl AsRef<Path>) -> std::io::Result<String> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::read_to_string(path)).await.unwrap()
}

pub async fn read(path: impl AsRef<Path>) -> std::io::Result<Vec<u8>> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::read(path)).await.unwrap()
}

pub async fn write(path: impl AsRef<Path>, data: impl AsRef<[u8]>) -> std::io::Result<()> {
  let path = path.as_ref().to_owned();
  let data = data.as_ref().to_vec();
  spawn_blocking(move || std::fs::write(path, data)).await.unwrap()
}

pub async fn metadata(path: impl AsRef<Path>) -> std::io::Result<std::fs::Metadata> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::metadata(path)).await.unwrap()
}

pub async fn remove_file(path: impl AsRef<Path>) -> std::io::Result<()> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::remove_file(path)).await.unwrap()
}

pub async fn create_dir_all(path: impl AsRef<Path>) -> std::io::Result<()> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::create_dir_all(path)).await.unwrap()
}

pub async fn rename(from: impl AsRef<Path>, to: impl AsRef<Path>) -> std::io::Result<()> {
  let from = from.as_ref().to_owned();
  let to = to.as_ref().to_owned();
  spawn_blocking(move || std::fs::rename(from, to)).await.unwrap()
}

pub async fn copy(from: impl AsRef<Path>, to: impl AsRef<Path>) -> std::io::Result<u64> {
  let from = from.as_ref().to_owned();
  let to = to.as_ref().to_owned();
  spawn_blocking(move || std::fs::copy(from, to)).await.unwrap()
}

pub async fn canonicalize(path: impl AsRef<Path>) -> std::io::Result<PathBuf> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::canonicalize(path)).await.unwrap()
}

pub async fn create_dir(path: impl AsRef<Path>) -> std::io::Result<()> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::create_dir(path)).await.unwrap()
}

pub async fn hard_link(original: impl AsRef<Path>, link: impl AsRef<Path>) -> std::io::Result<()> {
  let original = original.as_ref().to_owned();
  let link = link.as_ref().to_owned();
  spawn_blocking(move || std::fs::hard_link(original, link)).await.unwrap()
}

pub async fn read_dir(path: impl AsRef<Path>) -> std::io::Result<std::fs::ReadDir> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::read_dir(path)).await.unwrap()
}

pub async fn read_link(path: impl AsRef<Path>) -> std::io::Result<PathBuf> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::read_link(path)).await.unwrap()
}

pub async fn remove_dir(path: impl AsRef<Path>) -> std::io::Result<()> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::remove_dir(path)).await.unwrap()
}

pub async fn remove_dir_all(path: impl AsRef<Path>) -> std::io::Result<()> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::remove_dir_all(path)).await.unwrap()
}

pub async fn symlink_metadata(path: impl AsRef<Path>) -> std::io::Result<std::fs::Metadata> {
  let path = path.as_ref().to_owned();
  spawn_blocking(move || std::fs::symlink_metadata(path)).await.unwrap()
}
