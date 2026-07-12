use vstd::prelude::*;

verus! {

pub const SLAB_CAPACITY: usize = 65536;

#[verifier::reject_recursive_types(V)]
pub struct Slab<V: View> {
  pub inner: Vec<Option<V>>,
  pub offset: u64,
}

impl<V: View> View for Slab<V> {
  type V = Map<nat, V::V>;

  open spec fn view(&self) -> Map<nat, V::V> {
    Map::new(
      |k: nat| self.spec_contains(k),
      |k: nat| self.inner@[k - self.offset as nat]->Some_0@,
    )
  }
}

impl<V: View> Slab<V> {
  pub open spec fn spec_contains(&self, k: nat) -> bool {
    &&& self.offset as nat <= k
    &&& (k - self.offset as nat) < self.inner@.len()
    &&& self.inner@[k - self.offset as nat] is Some
  }

  pub open spec fn wf(&self) -> bool {
    true
  }

  pub fn new() -> (result: Self)
    ensures
      result@ == Map::<nat, V::V>::empty(),
      result.wf(),
  {
    let result = Slab {
      inner: Vec::new(),
      offset: 0,
    };
    proof {
      assert(result.inner@.len() == 0);
      assert(forall |k: nat| !result.spec_contains(k));
      assert(result@ =~= Map::<nat, V::V>::empty());
    }
    result
  }

  // Faithful leaf: prepend `old.offset - key` None slots and set offset = key.
  // Wraps resize_with + rotate_right. Spec pins the exact shift on inner@.
  #[cold]
  #[inline(never)]
  #[verifier::external_body]
  fn grow_front(&mut self, key: u64)
    requires key < old(self).offset,
    ensures
      self.offset == key,
      self.inner@.len() == old(self).inner@.len() + (old(self).offset - key),
      forall |j: int| 0 <= j < (old(self).offset - key) ==> self.inner@[j] is None,
      forall |j: int| 0 <= j < old(self).inner@.len() ==>
        self.inner@[j + (old(self).offset - key)] == old(self).inner@[j],
  {
    let extra = (self.offset - key) as usize;
    let old_len = self.inner.len();
    self.inner.resize_with(old_len + extra, || None);
    self.inner.rotate_right(extra);
    self.offset = key;
  }

  // Faithful leaf: grow inner (with None) so that index `rel` is in bounds,
  // preserving offset and all existing slots. Wraps resize_with.
  #[inline(always)]
  #[verifier::external_body]
  fn ensure_slot(&mut self, rel: u64)
    ensures
      self.offset == old(self).offset,
      (rel as int) < self.inner@.len(),
      self.inner@.len() >= old(self).inner@.len(),
      forall |j: int| 0 <= j < old(self).inner@.len() ==>
        self.inner@[j] == old(self).inner@[j],
      forall |j: int| old(self).inner@.len() <= j < self.inner@.len() ==>
        self.inner@[j] is None,
  {
    let idx = rel as usize;
    if idx >= self.inner.len() {
      self.inner.resize_with(idx + 1, || None);
    }
  }

  // Faithful leaf: set slot `rel` to Some(value), preserving offset.
  #[inline(always)]
  #[verifier::external_body]
  fn set_slot(&mut self, rel: u64, value: V)
    requires (rel as int) < old(self).inner@.len(),
    ensures
      self.offset == old(self).offset,
      self.inner@ == old(self).inner@.update(rel as int, Some(value)),
  {
    let idx = rel as usize;
    self.inner.set(idx, Some(value));
  }

  #[inline(always)]
  pub fn insert(&mut self, key: u64, value: V)
    requires
      old(self).wf(),
    ensures
      self@ == old(self)@.insert(key as nat, value@),
      self.wf(),
  {
    let ghost old_view = old(self)@;

    if self.inner.len() == 0 {
      self.offset = key;
      proof { assert(self@ =~= old_view); }
    } else if key < self.offset {
      let ghost pre = *self;
      self.grow_front(key);
      proof {
        let ex = pre.offset as int - key as int;
        assert forall |k: nat| self.spec_contains(k) <==> pre.spec_contains(k) by {
          let kk = k as int - key as int;
          let kp = k as int - pre.offset as int;
          if key as nat <= k && 0 <= kp && kp < pre.inner@.len() {
            assert(self.inner@[kp + ex] == pre.inner@[kp]);
            assert(kp + ex == kk);
          } else if key as nat <= k && kk < ex {
            assert(self.inner@[kk] is None);
          }
        };
        assert forall |k: nat| self.spec_contains(k) implies self@[k] == pre@[k] by {
          let kk = k as int - key as int;
          let kp = k as int - pre.offset as int;
          if kk < ex {
            assert(self.inner@[kk] is None);
          } else {
            assert(self.inner@[kp + ex] == pre.inner@[kp]);
            assert(kp + ex == kk);
          }
        };
        assert(self@ =~= old_view);
      }
    }

    assert(self.offset <= key);
    let rel = key - self.offset;

    let ghost pre_ensure = *self;
    self.ensure_slot(rel);
    proof {
      assert forall |k: nat| self.spec_contains(k) <==> pre_ensure.spec_contains(k) by {
        if self.offset as nat <= k && (k - self.offset as nat) < pre_ensure.inner@.len() {
          assert(self.inner@[k - self.offset as nat] == pre_ensure.inner@[k - self.offset as nat]);
        }
      };
      assert forall |k: nat| self.spec_contains(k) implies self@[k] == pre_ensure@[k] by {
        assert(self.inner@[k - self.offset as nat] == pre_ensure.inner@[k - self.offset as nat]);
      };
      assert(self@ =~= old_view);
    }

    let ghost pre_set = *self;
    self.set_slot(rel, value);
    proof {
      let kn = key as nat;
      assert(rel as nat == kn - self.offset as nat);
      assert forall |k: nat| self.spec_contains(k) <==> old_view.insert(kn, value@).contains_key(k) by {
        if self.offset as nat <= k && (k - self.offset as nat) < self.inner@.len() {
          if k == kn {
          } else {
            assert((k - self.offset as nat) != (kn - self.offset as nat));
            assert(self.inner@[k - self.offset as nat] == pre_set.inner@[k - self.offset as nat]);
          }
        }
      };
      assert forall |k: nat| self.spec_contains(k) implies
        self@[k] == old_view.insert(kn, value@)[k] by {
        if k == kn {
          assert(self.inner@[k - self.offset as nat] == Some(value));
        } else {
          assert((k - self.offset as nat) != (kn - self.offset as nat));
          assert(self.inner@[k - self.offset as nat] == pre_set.inner@[k - self.offset as nat]);
        }
      };
      assert(self@ =~= old_view.insert(kn, value@));
    }
  }

  #[inline(always)]
  pub fn get(&self, key: u64) -> (result: Option<&V>)
    ensures
      result.is_some() <==> self@.contains_key(key as nat),
      result.is_some() ==> result.unwrap()@ == self@[key as nat],
  {
    if key < self.offset {
      return None;
    }
    let diff = key - self.offset;
    if diff >= self.inner.len() as u64 {
      return None;
    }
    let idx = diff as usize;
    self.inner[idx].as_ref()
  }

  // external (not external_body): Verus cannot express `&mut` returns, so this
  // stays outside verification — but the body is SAFE code mirroring `get`
  // above (bounds-checked std indexing; no unsafe anywhere in this crate).
  #[inline(always)]
  #[verifier::external]
  pub fn get_mut(&mut self, key: u64) -> Option<&mut V> {
    if key < self.offset {
      return None;
    }
    let diff = key - self.offset;
    if diff >= self.inner.len() as u64 {
      return None;
    }
    self.inner[diff as usize].as_mut()
  }

  // Faithful leaf: take the Option at `idx`, leaving None there and all other
  // slots (and offset) unchanged. Wraps the irreducible mem::take-at-index.
  // Spec pins the exact effect on inner@.
  #[inline(always)]
  #[verifier::external_body]
  fn take_at(&mut self, idx: usize) -> (result: Option<V>)
    requires idx < old(self).inner@.len(),
    ensures
      self.offset == old(self).offset,
      self.inner@.len() == old(self).inner@.len(),
      self.inner@[idx as int] is None,
      forall |j: int| 0 <= j < self.inner@.len() && j != idx as int ==>
        self.inner@[j] == old(self).inner@[j],
      result == old(self).inner@[idx as int],
  {
    std::mem::take(&mut self.inner[idx])
  }

  #[inline(always)]
  pub fn remove(&mut self, key: u64) -> (result: Option<V>)
    requires old(self).wf(),
    ensures
      self@ == old(self)@.remove(key as nat),
      result.is_some() <==> old(self)@.contains_key(key as nat),
      result.is_some() ==> result.unwrap()@ == old(self)@[key as nat],
      self.wf(),
  {
    if key < self.offset {
      assert(!old(self).spec_contains(key as nat));
      assert(self@ =~= old(self)@.remove(key as nat));
      return None;
    }
    let diff = key - self.offset;
    if diff >= self.inner.len() as u64 {
      assert(!old(self).spec_contains(key as nat));
      assert(self@ =~= old(self)@.remove(key as nat));
      return None;
    }
    let idx = diff as usize;
    let result = self.take_at(idx);
    proof {
      let kn = key as nat;
      assert forall |k: nat| self@.contains_key(k) <==>
        old(self)@.remove(kn).contains_key(k)
      by {
        if self.offset as nat <= k && (k - self.offset as nat) < self.inner@.len() {
          if k == kn {
          } else {
            assert((k - self.offset as nat) != (kn - self.offset as nat));
          }
        }
      };
      assert forall |k: nat| self@.contains_key(k) implies
        self@[k] == old(self)@.remove(kn)[k]
      by {
        assert(k != kn);
        assert((k - self.offset as nat) != (kn - self.offset as nat));
      };
      assert(self@ =~= old(self)@.remove(kn));
    }
    result
  }

}

}
