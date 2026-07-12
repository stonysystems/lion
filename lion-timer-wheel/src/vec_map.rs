use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
pub struct VecMap<V: View> {
  pub inner: Vec<Option<V>>,
  pub offset: u64,
  pub count: usize,
}

// Occupancy: the number of Some slots. The exec `count` field mirrors this
// spec-side quantity (see `count_wf`), which is what makes O(1) `is_empty`
// verifiable instead of trusted.
pub closed spec fn occupancy<V>(s: Seq<Option<V>>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    occupancy(s.drop_last()) + if s.last() is Some { 1nat } else { 0nat }
  }
}

pub proof fn occupancy_all_none<V>(s: Seq<Option<V>>)
  requires forall |j: int| 0 <= j < s.len() ==> s[j] is None,
  ensures occupancy(s) == 0,
  decreases s.len()
{
  reveal(occupancy);
  if s.len() > 0 {
    occupancy_all_none(s.drop_last());
  }
}

pub proof fn occupancy_zero_all_none<V>(s: Seq<Option<V>>)
  requires occupancy(s) == 0,
  ensures forall |j: int| 0 <= j < s.len() ==> s[j] is None,
  decreases s.len()
{
  reveal(occupancy);
  if s.len() > 0 {
    occupancy_zero_all_none(s.drop_last());
    assert forall |j: int| 0 <= j < s.len() implies s[j] is None by {
      if j < s.len() - 1 {
        assert(s.drop_last()[j] is None);
      } else {
        assert(s[j] == s.last());
      }
    }
  }
}

pub proof fn occupancy_update<V>(s: Seq<Option<V>>, i: int, v: Option<V>)
  requires 0 <= i < s.len(),
  ensures occupancy(s.update(i, v)) ==
    occupancy(s)
      + (if v is Some { 1nat } else { 0nat })
      - (if s[i] is Some { 1nat } else { 0nat }),
  decreases s.len()
{
  reveal(occupancy);
  let s2 = s.update(i, v);
  if i == s.len() - 1 {
    assert(s2.drop_last() =~= s.drop_last());
  } else {
    assert(s2.drop_last() =~= s.drop_last().update(i, v));
    occupancy_update(s.drop_last(), i, v);
    assert(s2.last() == s.last());
  }
}

pub proof fn occupancy_append_nones<V>(s1: Seq<Option<V>>, s2: Seq<Option<V>>)
  requires
    s2.len() >= s1.len(),
    forall |j: int| 0 <= j < s1.len() ==> s2[j] == s1[j],
    forall |j: int| s1.len() <= j < s2.len() ==> s2[j] is None,
  ensures occupancy(s2) == occupancy(s1),
  decreases s2.len()
{
  reveal(occupancy);
  if s2.len() > s1.len() {
    assert(s2.last() is None);
    occupancy_append_nones(s1, s2.drop_last());
  } else if s2.len() > 0 {
    assert(s2 =~= s1);
  } else {
    assert(s2 =~= s1);
  }
}

pub proof fn occupancy_prepend_nones<V>(s1: Seq<Option<V>>, s2: Seq<Option<V>>, ex: int)
  requires
    ex >= 0,
    s2.len() == s1.len() + ex,
    forall |j: int| 0 <= j < ex ==> s2[j] is None,
    forall |j: int| 0 <= j < s1.len() ==> s2[j + ex] == s1[j],
  ensures occupancy(s2) == occupancy(s1),
  decreases s1.len()
{
  reveal(occupancy);
  if s1.len() == 0 {
    occupancy_all_none(s2);
  } else {
    assert(s2.last() == s1.last()) by {
      assert(s2[(s1.len() - 1) + ex] == s1[s1.len() - 1]);
    }
    assert forall |j: int| 0 <= j < s1.drop_last().len() implies
      s2.drop_last()[j + ex] == s1.drop_last()[j] by {
      assert(s2[j + ex] == s1[j]);
    }
    occupancy_prepend_nones(s1.drop_last(), s2.drop_last(), ex);
  }
}

impl<V: View> VecMap<V> {
  // Real abstraction: key k is present iff slot (k - offset) holds Some.
  pub open spec fn spec_contains(&self, k: u64) -> bool {
    &&& self.offset <= k
    &&& (k as int - self.offset as int) < self.inner@.len()
    &&& self.inner@[k as int - self.offset as int] is Some
  }

  // The exec `count` field equals the spec occupancy, and every slot is
  // addressable by a u64 key (offset + len does not run past u64::MAX + 1).
  // Established by `new`, preserved by `insert`/`remove`; what `is_empty`
  // needs to be verified rather than trusted.
  pub open spec fn count_wf(&self) -> bool {
    &&& self.count as nat == occupancy(self.inner@)
    &&& self.offset as int + self.inner@.len() <= u64::MAX as int + 1
  }
}

impl<V: View> View for VecMap<V> {
  type V = Map<u64, V>;

  open spec fn view(&self) -> Map<u64, V> {
    Map::new(
      |k: u64| self.spec_contains(k),
      |k: u64| self.inner@[k as int - self.offset as int]->Some_0,
    )
  }
}

impl<V: View + Copy> VecMap<V> {

  pub exec fn new() -> (result: Self)
    ensures
      result@ == Map::<u64, V>::empty(),
      result.count_wf(),
  {
    let result = VecMap { inner: Vec::new(), offset: 0, count: 0 };
    proof {
      assert(result.inner@.len() == 0);
      assert(forall |k: u64| !result.spec_contains(k));
      assert(result@ =~= Map::<u64, V>::empty());
      occupancy_all_none(result.inner@);
    }
    result
  }

  // Faithful leaf: prepend `old.offset - key` None slots and set offset = key.
  // Wraps the Vec rebuild. Spec pins the exact shift on inner@.
  #[cold]
  #[inline(never)]
  #[verifier::external_body]
  fn grow_front(&mut self, key: u64)
    requires key < old(self).offset,
    ensures
      self.offset == key,
      self.count == old(self).count,
      self.inner@.len() == old(self).inner@.len() + (old(self).offset - key),
      forall |j: int| 0 <= j < (old(self).offset - key) ==> self.inner@[j] is None,
      forall |j: int| 0 <= j < old(self).inner@.len() ==>
        self.inner@[j + (old(self).offset - key)] == old(self).inner@[j],
  {
    let extra = (self.offset - key) as usize;
    let mut new_inner = Vec::with_capacity(self.inner.len() + extra);
    new_inner.resize(extra, None);
    new_inner.append(&mut self.inner);
    self.inner = new_inner;
    self.offset = key;
  }

  // Faithful leaf: grow inner (with None) so index `rel` is in bounds,
  // preserving offset and existing slots. Wraps resize.
  #[inline(always)]
  #[verifier::external_body]
  fn ensure_slot(&mut self, rel: u64)
    ensures
      self.offset == old(self).offset,
      self.count == old(self).count,
      (rel as int) < self.inner@.len(),
      self.inner@.len() >= old(self).inner@.len(),
      self.inner@.len() as int == if old(self).inner@.len() > rel as int
        { old(self).inner@.len() as int } else { rel as int + 1 },
      forall |j: int| 0 <= j < old(self).inner@.len() ==>
        self.inner@[j] == old(self).inner@[j],
      forall |j: int| old(self).inner@.len() <= j < self.inner@.len() ==>
        self.inner@[j] is None,
  {
    let idx = rel as usize;
    if idx >= self.inner.len() {
      self.inner.resize(idx + 1, None);
    }
  }

  // Faithful leaf: set slot `rel` to Some(value), preserving offset.
  // The `count` field (occupancy, only read by is_empty) is maintained here so
  // verified code never incurs count arithmetic obligations.
  #[inline(always)]
  #[verifier::external_body]
  fn set_slot(&mut self, rel: u64, value: V)
    requires (rel as int) < old(self).inner@.len(),
    ensures
      self.offset == old(self).offset,
      self.inner@ == old(self).inner@.update(rel as int, Some(value)),
      self.count as int == old(self).count as int
        + if old(self).inner@[rel as int] is Some { 0int } else { 1int },
  {
    let idx = rel as usize;
    if self.inner[idx].is_none() {
      self.count += 1;
    }
    self.inner[idx] = Some(value);
  }

  // Faithful leaf: take slot `rel`, leaving None, preserving offset/other slots.
  // Maintains `count` (see set_slot).
  #[inline(always)]
  #[verifier::external_body]
  fn take_at(&mut self, rel: u64) -> (result: Option<V>)
    requires (rel as int) < old(self).inner@.len(),
    ensures
      self.offset == old(self).offset,
      self.inner@.len() == old(self).inner@.len(),
      self.inner@[rel as int] is None,
      forall |j: int| 0 <= j < self.inner@.len() && j != rel as int ==>
        self.inner@[j] == old(self).inner@[j],
      result == old(self).inner@[rel as int],
      self.count as int == old(self).count as int
        - if old(self).inner@[rel as int] is Some { 1int } else { 0int },
  {
    let idx = rel as usize;
    let result = self.inner[idx].take();
    if result.is_some() {
      self.count -= 1;
    }
    result
  }

  #[inline(always)]
  pub exec fn insert(&mut self, key: u64, value: V)
    ensures
      self@ == old(self)@.insert(key, value),
      old(self).count_wf() ==> self.count_wf(),
  {
    let ghost old_view = old(self)@;

    if self.inner.len() == 0 {
      self.offset = key;
      proof { assert(self@ =~= old_view); }
    } else if key < self.offset {
      let ghost pre = *self;
      self.grow_front(key);
      proof {
        occupancy_prepend_nones(pre.inner@, self.inner@, pre.offset as int - key as int);
        let ex = pre.offset as int - key as int;
        assert forall |k: u64| self.spec_contains(k) <==> pre.spec_contains(k) by {
          let kk = k as int - key as int;
          let kp = k as int - pre.offset as int;
          if key <= k && 0 <= kp && kp < pre.inner@.len() {
            assert(self.inner@[kp + ex] == pre.inner@[kp]);
            assert(kp + ex == kk);
          } else if key <= k && kk < ex {
            assert(self.inner@[kk] is None);
          }
        };
        assert forall |k: u64| self.spec_contains(k) implies self@[k] == pre@[k] by {
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
      occupancy_append_nones(pre_ensure.inner@, self.inner@);
      assert forall |k: u64| self.spec_contains(k) <==> pre_ensure.spec_contains(k) by {
        if self.offset <= k && (k as int - self.offset as int) < pre_ensure.inner@.len() {
          assert(self.inner@[k as int - self.offset as int]
            == pre_ensure.inner@[k as int - self.offset as int]);
        }
      };
      assert forall |k: u64| self.spec_contains(k) implies self@[k] == pre_ensure@[k] by {
        assert(self.inner@[k as int - self.offset as int]
          == pre_ensure.inner@[k as int - self.offset as int]);
      };
      assert(self@ =~= old_view);
    }

    let ghost pre_set = *self;
    self.set_slot(rel, value);
    proof {
      assert forall |k: u64| self.spec_contains(k) <==> old_view.insert(key, value).contains_key(k) by {
        if self.offset <= k && (k as int - self.offset as int) < self.inner@.len() {
          if k == key {
          } else {
            assert((k as int - self.offset as int) != (key as int - self.offset as int));
            assert(self.inner@[k as int - self.offset as int]
              == pre_set.inner@[k as int - self.offset as int]);
          }
        }
      };
      assert forall |k: u64| self.spec_contains(k) implies
        self@[k] == old_view.insert(key, value)[k] by {
        if k == key {
          assert(self.inner@[k as int - self.offset as int] == Some(value));
        } else {
          assert((k as int - self.offset as int) != (key as int - self.offset as int));
          assert(self.inner@[k as int - self.offset as int]
            == pre_set.inner@[k as int - self.offset as int]);
        }
      };
      assert(self@ =~= old_view.insert(key, value));
      occupancy_update(pre_set.inner@, rel as int, Some(value));
      if old(self).count_wf() {
        assert(self.count_wf()) by {
          assert(occupancy(pre_set.inner@) == occupancy(old(self).inner@));
          assert(self.offset as int + rel as int + 1 <= key as int + 1);
        }
      }
    }
  }

  #[inline(always)]
  pub exec fn get(&self, key: &u64) -> (result: Option<&V>)
    ensures
      result.is_some() <==> self@.contains_key(*key),
      result.is_some() ==> *result.unwrap() == self@[*key],
  {
    let key = *key;
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

  #[inline(always)]
  pub exec fn remove(&mut self, key: &u64) -> (result: Option<V>)
    ensures
      self@ == old(self)@.remove(*key),
      result.is_some() <==> old(self)@.contains_key(*key),
      result.is_some() ==> result.unwrap() == old(self)@[*key],
      old(self).count_wf() ==> self.count_wf(),
  {
    let key = *key;
    if key < self.offset {
      assert(!old(self).spec_contains(key));
      assert(self@ =~= old(self)@.remove(key));
      return None;
    }
    let diff = key - self.offset;
    if diff >= self.inner.len() as u64 {
      assert(!old(self).spec_contains(key));
      assert(self@ =~= old(self)@.remove(key));
      return None;
    }
    let rel = diff;
    let result = self.take_at(rel);
    proof {
      assert(self.inner@ =~= old(self).inner@.update(rel as int, None));
      occupancy_update(old(self).inner@, rel as int, None::<V>);
      assert forall |k: u64| self@.contains_key(k) <==>
        old(self)@.remove(key).contains_key(k)
      by {
        if self.offset <= k && (k as int - self.offset as int) < self.inner@.len() {
          if k == key {
          } else {
            assert((k as int - self.offset as int) != (key as int - self.offset as int));
          }
        }
      };
      assert forall |k: u64| self@.contains_key(k) implies
        self@[k] == old(self)@.remove(key)[k]
      by {
        assert(k != key);
        assert((k as int - self.offset as int) != (key as int - self.offset as int));
      };
      assert(self@ =~= old(self)@.remove(key));
    }
    result
  }

  #[inline(always)]
  pub exec fn contains_key(&self, key: &u64) -> (result: bool)
    ensures result == self@.contains_key(*key),
  {
    let key = *key;
    if key < self.offset {
      return false;
    }
    let diff = key - self.offset;
    if diff >= self.inner.len() as u64 {
      return false;
    }
    let idx = diff as usize;
    self.inner[idx].is_some()
  }

  // VERIFIED O(1) emptiness via the count/occupancy coupling (count_wf):
  // count == 0 ⟺ occupancy == 0 ⟺ every slot None ⟺ the map view is empty.
  #[inline]
  pub exec fn is_empty(&self) -> (result: bool)
    requires self.count_wf(),
    ensures result == (self@ == Map::<u64, V>::empty()),
  {
    let r = self.count == 0;
    proof {
      if r {
        occupancy_zero_all_none(self.inner@);
        assert(forall |k: u64| !self.spec_contains(k));
        assert(self@ =~= Map::<u64, V>::empty());
      } else {
        assert(exists |j: int| 0 <= j < self.inner@.len() && self.inner@[j] is Some) by {
          if forall |j: int| 0 <= j < self.inner@.len() ==> self.inner@[j] is None {
            occupancy_all_none(self.inner@);
          }
        }
        let j = choose |j: int| 0 <= j < self.inner@.len() && self.inner@[j] is Some;
        let ki: int = self.offset as int + j;
        assert(ki <= u64::MAX as int);
        let k = ki as u64;
        assert(self.spec_contains(k));
        assert(self@.contains_key(k));
        assert(!Map::<u64, V>::empty().contains_key(k));
      }
    }
    r
  }
}

}
