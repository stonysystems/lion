use crate::types::ResourceId;
use std::cell::RefCell;
use std::collections::HashMap;

const READABLE: u8 = 0x01;
const WRITABLE: u8 = 0x02;

// Per-resource readiness flags, keyed by rid. An entry exists only between
// `init_readiness` (after a successful io registration) and `remove_readiness`
// (on deregistration), so the table holds one byte per LIVE io resource. Rids
// are never reused, so an entry indexed by rid in a window would instead grow
// with every rid ever allocated. `mark_*` / `clear_*` touch existing entries
// only: a stale event for a deregistered rid is a no-op, and a rid that was
// never initialised (a timer) reads as not ready.
thread_local! {
  static IO_READINESS: RefCell<HashMap<u64, u8>> = RefCell::new(HashMap::new());
}

pub fn init_readiness(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    r.borrow_mut().insert(resource_id.0, READABLE | WRITABLE);
  });
}

pub fn remove_readiness(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    r.borrow_mut().remove(&resource_id.0);
  });
}

pub fn mark_readable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    if let Some(f) = r.borrow_mut().get_mut(&resource_id.0) {
      *f |= READABLE;
    }
  });
}

pub fn mark_writable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    if let Some(f) = r.borrow_mut().get_mut(&resource_id.0) {
      *f |= WRITABLE;
    }
  });
}

pub fn is_readable(resource_id: ResourceId) -> bool {
  IO_READINESS.with(|r| {
    r.borrow().get(&resource_id.0).is_some_and(|f| (f & READABLE) != 0)
  })
}

pub fn is_writable(resource_id: ResourceId) -> bool {
  IO_READINESS.with(|r| {
    r.borrow().get(&resource_id.0).is_some_and(|f| (f & WRITABLE) != 0)
  })
}

pub fn clear_readable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    if let Some(f) = r.borrow_mut().get_mut(&resource_id.0) {
      *f &= !READABLE;
    }
  });
}

pub fn clear_writable(resource_id: ResourceId) {
  IO_READINESS.with(|r| {
    if let Some(f) = r.borrow_mut().get_mut(&resource_id.0) {
      *f &= !WRITABLE;
    }
  });
}
