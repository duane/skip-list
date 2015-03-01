// Copyright 2014 The Rust Project Developers. See the licenses/rust-COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

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