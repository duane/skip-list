// Copyright 2015 Duane R. Bailey
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![crate_type = "lib"]
#![feature(box_syntax)]
#![feature(core)]
#![allow(dead_code)]

extern crate rand;

pub mod list {

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

/// This is an implementation of a map with probably low runtime.
///
/// With the default p = 0.5, a node is constructed with random height.
/// Insertion is O(log(n)) where n is the number of nodes in the list.
/// Lookup and removal are also O(log(n)).
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

struct NodePtrIterator<K, V> {
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
  /// Makes a new, empty SkipList with sensible defaults.
  ///
  /// The new list has p = 0.5, max_level = std::usize::MAX.
  ///
  /// # Examples
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// assert!(a.is_empty());
  /// ```
  pub fn new() -> SkipList<K, V> {
    SkipList::<K, V>::new_skip_list(MAX, DEFAULT_P)
  }

  /// Makes a new, empty SkipList with specified p and max_level.
  ///
  /// # Examples
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new_skip_list(32, 0.25);
  /// ```
  pub fn new_skip_list(max_level: usize, p: f32) -> SkipList<K, V> {
    SkipList {
      rng: StdRng::new().unwrap(),
      p: p,
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
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// a.insert("foo", 0);
  /// 
  /// assert!(a.get(&"foo") == Some(&0));
  ///
  /// a.remove(&"foo");
  /// 
  /// assert!(a.get(&"foo") == None);
  /// ```
  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
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

  /// Fetch the value from the skip list indexed by key. Return none if the key is not in the skip list.
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// a.insert("foo", 0);
  /// 
  /// assert!(a.get(&"foo") == Some(&0));
  ///
  /// a.remove(&"foo");
  /// 
  /// assert!(a.get(&"foo") == None);
  /// ```
  pub fn get<'s>(&'s mut self, key: &K) -> Option<&'s V> {
    unsafe {
      match self.search(key) {
        (_, node) if !node.is_null() => Some((*node).value.get()),
        _ => None
      }
    }
  }

  /// Delete the value from the skip list.
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// a.insert("foo", 0);
  /// 
  /// assert!(a.get(&"foo") == Some(&0));
  /// assert!(a.len() == 1);
  ///
  /// a.remove(&"foo");
  /// 
  /// assert!(a.get(&"foo") == None);
  /// assert!(a.len() == 0);
  /// ```
  pub fn remove(&mut self, key: &K) -> Option<V> {
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

  /// Acquire an iterator on this skip list.
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// a.insert("foo", 0);
  /// a.insert("bar", 1);
  /// 
  /// let vals: Vec<usize> = a.iter().map(|(k, v)| *v).collect();
  /// assert!(&vals == &[1, 0]);
  /// ```
  pub fn iter<'s>(&'s mut self) -> Iter<K, V> {
    Iter {
      inner: NodePtrIterator {
        node: if self.len() > 0 { self.head[0] } else { ptr::null_mut() },
        remaining: self.len()
      }
    }
  }

  /// Acquire a mutable iterator on this skip list.
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// a.insert("foo", 0);
  /// a.insert("bar", 1);
  /// 
  /// for (key, value) in a.iter_mut() {
  ///   if (key == &"foo") {
  ///     *value += 10;
  ///   }
  /// }
  /// assert!(a.get(&"foo") == Some(&10));
  /// assert!(a.get(&"bar") == Some(&1));
  ///
  /// ```
  pub fn iter_mut<'s>(&'s mut self) -> MutIter<K, V> {
    MutIter {
      inner: NodePtrIterator {
        node: if self.len() > 0 { self.head[0] } else { ptr::null_mut() },
        remaining: self.len()
      }
    }
  }

  /// Acquire a copying iterator on this skip list.
  ///
  /// This is useful for copying the skip list into some other format.
  ///
  /// ```
  /// use skip_list::list::SkipList;
  /// use std::collections::BTreeMap;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// a.insert("foo", 0);
  /// a.insert("bar", 1);
  /// let b: BTreeMap<&str, usize> = a.into_iter().collect();
  /// assert!(b.get("foo") == Some(&0));
  /// assert!(b.get("bar") == Some(&1));
  /// ```
  pub fn into_iter<'s>(&'s mut self) -> CopyIter<K, V> {
    CopyIter {
      inner: NodePtrIterator {
        node: if self.len() > 0 { self.head[0] } else { ptr::null_mut() },
        remaining: self.len()
      }
    }
  }

  /// Returns true iff the skip list is empty.
  ///
  /// # Example
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// assert!(a.is_empty());
  /// a.insert("foo", 0);
  /// assert!(!a.is_empty());
  /// ```
  pub fn is_empty(&self) -> bool {
    self.size == 0
  }

  /// The number of items in the skip list.
  ///
  /// # Example
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// assert!(a.len() == 0);
  /// a.insert("foo", 0);
  /// a.insert("bar", 1);
  /// assert!(a.len() == 2);
  /// ```
  pub fn len(&self) -> usize {
    self.size
  }

  /// Returns true iff the skip list contains `key`.
  ///
  /// # Example
  ///
  /// ```
  /// use skip_list::list::SkipList;
  ///
  /// let mut a = SkipList::<&str, usize>::new();
  /// assert!(!a.contains("foo"));
  /// a.insert("foo", 0);
  /// assert!(a.contains("foo"));
  /// ```
  pub fn contains(&mut self, key: K) -> bool {
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

}