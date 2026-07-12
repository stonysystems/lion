use crate::types::ResourceId;
use std::cell::RefCell;

const READABLE: u8 = 0x01;
const WRITABLE: u8 = 0x02;

thread_local! {
  static IO_READINESS: RefCell<Vec<u8>> = RefCell::new(Vec::new());
}

pub fn init_readiness(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    let mut v = r.borrow_mut();
    let idx = resource_id.0 as usize;
    if idx >= v.len() {
      v.resize(idx + 1, 0);
    }
    v[idx] = READABLE | WRITABLE;
  });
}

pub fn mark_readable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    let mut v = r.borrow_mut();
    let idx = resource_id.0 as usize;
    if idx < v.len() {
      v[idx] |= READABLE;
    }
  });
}

pub fn mark_writable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    let mut v = r.borrow_mut();
    let idx = resource_id.0 as usize;
    if idx < v.len() {
      v[idx] |= WRITABLE;
    }
  });
}

pub fn is_readable(resource_id: ResourceId) -> bool {
  IO_READINESS.with(|r| {
    let v = r.borrow();
    let idx = resource_id.0 as usize;
    idx < v.len() && (v[idx] & READABLE) != 0
  })
}

pub fn is_writable(resource_id: ResourceId) -> bool {
  IO_READINESS.with(|r| {
    let v = r.borrow();
    let idx = resource_id.0 as usize;
    idx < v.len() && (v[idx] & WRITABLE) != 0
  })
}

pub fn clear_readable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    let mut v = r.borrow_mut();
    let idx = resource_id.0 as usize;
    if idx < v.len() {
      v[idx] &= !READABLE;
    }
  });
}

pub fn clear_writable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    let mut v = r.borrow_mut();
    let idx = resource_id.0 as usize;
    if idx < v.len() {
      v[idx] &= !WRITABLE;
    }
  });
}
