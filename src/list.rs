// Copyright (c) 2015 by Duane R. Bailey.

use rand::{StdRng, Rng};
use std::mem;
use std::iter::{Repeat, repeat};
use std::usize::MAX;
use std::cmp::Ordering;
use std::iter::IteratorExt;
use std::ptr::{PtrExt, Unique};
use std::ptr;
use std::ops::Deref;
use std::iter::FromIterator;
use std::iter::IntoIterator;

/// This is a skip list.
pub struct SkipList<K: Ord, V> {
  rng: StdRng,
  p: f32,
  size: usize,
  head: Vec<*mut SkipListNode<K, V>>,
  max_level: usize
}

const RANGE_MIN: f32 = 0.0f32;
const RANGE_MAX: f32 = 1.0f32;
const DEFAULT_P: f32 = 0.5f32;

/// Nodes are either head nodes (a singleton), tail nodes (also a singleton), or a value-bearing node.
struct SkipListNode<K, V> {
  key: Unique<K>,
  value: Unique<V>,
  next: Vec<*mut SkipListNode<K, V>>
}

// Public iterators

pub struct NodePtrIterator<K, V> {
  node: *mut SkipListNode<K, V>,
  remaining: usize
}

pub struct Iter<K, V> {
  inner: NodePtrIterator<K, V>
}

pub struct MutIter<K, V> {
  inner: NodePtrIterator<K, V>
}

pub struct CopyIter<K, V> {
  inner: NodePtrIterator<K, V>
}

// Iterator implementations

impl<K, V> Iterator for NodePtrIterator<K, V> {
  type Item = (*mut K, *mut V);

  fn next(&mut self) -> Option<(*mut K, *mut V)> {
    unsafe {
      if self.node.is_null() {
        None
      } else {
        let node = &mut*self.node;
        self.node = node.next[0];
        self.remaining -= 1;
        Some((*node.key.deref(), *node.value.deref()))
      }
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.remaining, Some(self.remaining))
  }
}

impl<'s, K, V> Iterator for Iter<K, V> {
  type Item = (&'s K, &'s V);

  fn next(&mut self) -> Option<(&'s K, &'s V)> {
    unsafe {
      self.inner.next().map(|(k, v)| (&*k, &*v))
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<'s, K, V> Iterator for MutIter<K, V> {
  type Item = (&'s K, &'s mut V);

  fn next(&mut self) -> Option<(&'s K, &'s mut V)> {
    unsafe {
      self.inner.next().map(|(k, v)| (&*k, &mut *v))
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<K, V> Iterator for CopyIter<K, V> {
  type Item = (K, V);

  fn next(&mut self) -> Option<(K, V)> {
    unsafe {
      self.inner.next().map(|(k, v)| (ptr::read(k), ptr::read(v)))
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

// Skip list implementation

impl<K: Ord, V> SkipList<K, V> {
  pub fn new() -> SkipList<K, V> {
    SkipList::<K, V>::new_with_max_level(MAX)
  }

  pub fn new_with_max_level(max_level: usize) -> SkipList<K, V> {
    SkipList {
      rng: StdRng::new().unwrap(),
      p: DEFAULT_P,
      size: 0,
      head: vec!(),
      max_level: max_level
    }
  }

  /// Generate a random height.
  ///
  /// Generate a random height from the number of consecutive numbers less than p, and no greater than max_level.
  fn random_height(&mut self, p: f32) -> usize {
    let mut height = 1usize;
    let mut r = self.rng.gen_range(RANGE_MIN, RANGE_MAX);
    while r < p && height <= self.max_level {
      height += 1;
      r = self.rng.gen_range(RANGE_MIN, RANGE_MAX);
    }
    height
  }

  /// Returns (after_nodes, is_node).
  unsafe fn search(&mut self, key: &K) -> (Vec<*mut SkipListNode<K, V>>, *mut SkipListNode<K, V>) {
    let num_levels = self.head.len();
    if num_levels == 0 {
      return (vec!(), ptr::null_mut());
    }
    let mut level = (num_levels - 1) as isize;
    let mut after_nodes: Vec<*mut SkipListNode<K, V>> = vec!();
    let mut is_node: *mut SkipListNode<K, V> = ptr::null_mut();

    after_nodes.extend(repeat(ptr::null_mut()).take(num_levels));

    while level >= 0 {
      let prev_node = after_nodes[level as usize];
      let cur_node = if prev_node.is_null() {
        self.head[level as usize]
      } else {
        (*prev_node).next[level as usize]
      };

      if !cur_node.is_null() {
        let ordering = (*cur_node).key.get().cmp(key);
        match ordering {
          Ordering::Less => {
            after_nodes[level as usize] = cur_node;
            continue;
          }
          Ordering::Equal => is_node = cur_node,
          Ordering::Greater => ()
        }
      }
      level -= 1;
    }
    (after_nodes, is_node)
  }

  /// Insert a new value into the skip list.
  fn insert(&mut self, key: K, value: V) -> Option<V> {
    unsafe {
      match self.search(&key) {
        (ref mut after_nodes, is_node) if is_node.is_null() => {
          let height = self.head.len();
          let p = self.p;
          let random_height = self.random_height(p);
          assert!(random_height >= 1);
          let mut next_nodes: Vec<*mut SkipListNode<K, V>> = vec!();

          let key_ptr = Unique::new(mem::transmute(box key));
          let value_ptr = Unique::new(mem::transmute(box value));
          let node_struct = SkipListNode::<K, V>{
            key: key_ptr,
            value: value_ptr,
            next: vec!()
          };
          let new_node: *mut SkipListNode<K, V> = mem::transmute(box node_struct);

          for (i, node) in after_nodes.iter().enumerate() {
            if node.is_null() {
              next_nodes.push(self.head[i]);
              self.head[i] = new_node;
            } else {
              next_nodes.push((**node).next[i]);
              (**node).next[i] = new_node;
            }
          }

          let additional_nodes = (random_height as isize) - (height as isize);
          if additional_nodes > 0 {
            let next_nodes_repeat: Repeat<*mut SkipListNode<K, V>> = repeat(ptr::null_mut());
            next_nodes.extend(next_nodes_repeat.take(additional_nodes as usize));
            let head_nodes_repeat: Repeat<*mut SkipListNode<K, V>> = repeat(new_node);
            self.head.extend(head_nodes_repeat.take(additional_nodes as usize));
          }
          (*new_node).next = next_nodes;
          self.size += 1;
          None
        }
        (_, is_node) => {
          let ret_ptr = *(*is_node).value.deref();
          let ret = ptr::read(ret_ptr);
          drop(ret_ptr);
          (*is_node).value = Unique::new(mem::transmute(box value));
          Some(ret)
        }
      }
    }
  }

  /// Fetch the value from the skip list.
  fn get<'s>(&'s mut self, key: &K) -> Option<&'s V> {
    unsafe {
      match self.search(key) {
        (_, node) if !node.is_null() => Some((*node).value.get()),
        _ => None
      }
    }
  }

  /// Delete the value from the skip list.
  fn remove(&mut self, key: &K) -> Option<V> {
    unsafe {
      match self.search(key) {
        (ref mut after_nodes, node) if !node.is_null() => {
          for (i, after_node) in after_nodes.iter().take((*node).next.len()).enumerate() {
            let next_node = (*node).next[i];
            if after_node.is_null() {
              self.head[i] = next_node;
            } else {
              (**after_node).next[i] = next_node;
            }
          }
          drop(*(*node).key.deref());
          let ret_ptr = *(*node).value.deref();
          let ret = ptr::read(ret_ptr);
          drop(ret_ptr);
          drop(node);
          self.size -= 1;
          Some(ret)
        },
        _ => None
      }
    }
  }

  pub fn iter<'s>(&'s mut self) -> Iter<K, V> {
    Iter {
      inner: NodePtrIterator {
        node: if self.len() > 0 { self.head[0] } else { ptr::null_mut() },
        remaining: self.len()
      }
    }
  }

  pub fn iter_mut<'s>(&'s mut self) -> MutIter<K, V> {
    MutIter {
      inner: NodePtrIterator {
        node: if self.len() > 0 { self.head[0] } else { ptr::null_mut() },
        remaining: self.len()
      }
    }
  }

  /// Acquire an in-order iterator from the skip list.
  pub fn into_iter<'s>(&'s mut self) -> CopyIter<K, V> {
    CopyIter {
      inner: NodePtrIterator {
        node: if self.len() > 0 { self.head[0] } else { ptr::null_mut() },
        remaining: self.len()
      }
    }
  }

  /// The number of items in the skip list.
  pub fn len(&self) -> usize {
    self.size
  }

  /// Returns true iff the skip list contains `key`.
  fn contains(&mut self, key: K) -> bool {
    unsafe {
      match self.search(&key) {
        (_, node) => !node.is_null()
      }
    }
  }
}

impl<K: Ord, V> FromIterator<(K, V)> for SkipList<K, V> {
    fn from_iter<T: IntoIterator<Item=(K, V)>>(iter: T) -> SkipList<K, V> {
        let mut map = SkipList::new();
        map.extend(iter);
        map
    }
}

impl<K: Ord, V> Extend<(K, V)> for SkipList<K, V> {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}


#[cfg(test)]
mod test {
  use list::*;

  #[test]
  fn basic_test_large() {
    let mut map = SkipList::new();
    let size = 10000;
    assert_eq!(map.len(), 0);

    for i in 0..size {
        assert_eq!(map.insert(i, 10*i), None);
        assert_eq!(map.len(), i + 1);
    }

    for i in 0..size {
        assert_eq!(map.get(&i).unwrap(), &(i*10));
    }

    for i in size..size*2 {
        assert_eq!(map.get(&i), None);
    }

    for i in 0..size {
        assert_eq!(map.insert(i, 100*i), Some(10*i));
        assert_eq!(map.len(), size);
    }

    for i in 0..size {
        assert_eq!(map.get(&i).unwrap(), &(i*100));
    }

    for i in 0..size/2 {
        assert_eq!(map.remove(&(i*2)), Some(i*200));
        assert_eq!(map.len(), size - i - 1);
    }

    for i in 0..size/2 {
        assert_eq!(map.get(&(2*i)), None);
        assert_eq!(map.get(&(2*i+1)).unwrap(), &(i*200 + 100));
    }

    for i in 0..size/2 {
        assert_eq!(map.remove(&(2*i)), None);
        assert_eq!(map.remove(&(2*i+1)), Some(i*200 + 100));
        assert_eq!(map.len(), size/2 - i - 1);
    }
  }

  #[test]
  fn test_iter() {
    let size = 10000usize;

    // Forwards
    let mut map: SkipList<usize, usize> = range(0, size).map(|i| (i, i)).collect();

    {
        let mut iter = map.iter();
        for i in range(0, size) {
            assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
            assert_eq!(iter.next().unwrap(), (&i, &i));
        }
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

    {
        let mut iter = map.iter_mut();
        for i in range(0, size) {
            assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
            assert_eq!(iter.next().unwrap(), (&i, &mut (i + 0)));
        }
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

    {
        let mut iter = map.into_iter();
        for i in range(0, size) {
            assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
            assert_eq!(iter.next().unwrap(), (i, i));
        }
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

  }

  #[test]
  fn test_basic_small() {
    let mut map = SkipList::new();
    assert_eq!(map.remove(&1), None);
    assert_eq!(map.get(&1), None);
    assert_eq!(map.insert(1, 1), None);
    assert_eq!(map.get(&1), Some(&1));
    assert_eq!(map.insert(1, 2), Some(1));
    assert_eq!(map.get(&1), Some(&2));
    assert_eq!(map.insert(2, 4), None);
    assert_eq!(map.get(&2), Some(&4));
    assert_eq!(map.remove(&1), Some(2));
    assert_eq!(map.remove(&2), Some(4));
    assert_eq!(map.remove(&1), None);
  }

  /*#[test]
  fn iter_test() {
    let mut list = SkipList::<usize>::new();
    assert!(list.iter().next().is_none());
    list.insert(2);
    let vec: Vec<usize> = FromIterator::from_iter(list.copy_iter());
    assert!(vec.eq(&vec![2]));
    list.insert(1);
    let vec2: Vec<usize> = FromIterator::from_iter(list.copy_iter());
    assert!(vec2.eq(&vec![1,2]));
    list.insert(3);
    let vec3: Vec<usize> = FromIterator::from_iter(list.copy_iter());
    assert!(vec3.eq(&vec![1,2,3]));
    list.delete(2);
    let vec4: Vec<usize> = FromIterator::from_iter(list.copy_iter());
    assert!(vec4.eq(&vec![1,3]));
  }*/
}