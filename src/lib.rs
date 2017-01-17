use std::ops::Index;
use std::mem;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

impl Color {
    fn flip(&mut self) {
        match *self {
            Color::Red => *self = Color::Black,
            Color::Black => *self = Color::Red,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LLRB<K: Ord, V> {
    color: Color,
    kv: Option<(K, V)>,
    left: Option<Box<LLRB<K, V>>>,
    right: Option<Box<LLRB<K, V>>>,
}

impl<K: Ord, V> Default for LLRB<K, V> {
    fn default() -> LLRB<K, V> {
        LLRB {
            color: Color::Red,
            kv: None,
            left: None,
            right: None,
        }
    }
}

impl<'a, K: Ord, V> Index<&'a K> for LLRB<K, V>
    where K: Ord
{
    type Output = V;

    #[inline]
    fn index(&self, key: &K) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K: Ord, V> LLRB<K, V> {
    pub fn new() -> LLRB<K, V> {
        LLRB::default()
    }

    fn rotate_left(&mut self) {
        if !is_red(&self.right) {
            return;
        }

        let mut right = self.right.take().unwrap();
        self.color.flip();
        right.color.flip();
        self.right = right.left.take();
        mem::swap(self, &mut *right);
        self.left = Some(right);
    }

    fn rotate_right(&mut self) {
        if !is_red(&self.left) {
            return;
        }

        let mut left = self.left.take().unwrap();
        self.color.flip();
        left.color.flip();
        self.left = left.right.take();
        mem::swap(self, &mut *left);
        self.right = Some(left);
    }

    fn color_flip(&mut self) {
        self.color.flip();
        if let Some(ref mut r) = self.right {
            r.color.flip();
        }
        if let Some(ref mut l) = self.left {
            l.color.flip();
        }
    }

    fn fix_up(&mut self) {}

    fn move_red_right(&mut self) {}

    fn move_red_left(&mut self) {}

    fn is_double_left_red(&self) -> bool {
        if let Some(ref l) = self.left {
            if l.color == Color::Red && is_red(&l.left) {
                return true;
            }
        }
        false

    }


    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the tree's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut tree = LLRB::new();
    /// tree.insert(1, "a");
    /// assert_eq!(tree.get(&1), Some(&"a"));
    /// assert_eq!(tree.get(&2), None);
    /// ```
    pub fn get(&self, k: &K) -> Option<&V> {
        if let Some(ref kv) = self.kv {
            if &kv.0 == k {
                Some(&kv.1)
            } else if k < &kv.0 {
                if let Some(ref right) = self.right {
                    right.get(k)
                } else {
                    None
                }
            } else {
                if let Some(ref left) = self.left {
                    left.get(k)
                } else {
                    None
                }
            }
        } else {
            None
        }
    }

    /// Returns true if the tree contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the tree's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut tree = LLRB::new();
    /// tree.insert(1, "a");
    /// assert_eq!(tree.contains_key(&1), true);
    /// assert_eq!(tree.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, k: &K) -> bool {
        self.get(k).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the tree's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut tree = LLRB::new();
    /// tree.insert(1, "a");
    /// if let Some(x) = tree.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(tree[&1], "b");
    /// ```
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        if let Some(ref mut kv) = self.kv {
            if &kv.0 == k {
                Some(&mut kv.1)
            } else if k < &kv.0 {
                if let Some(ref mut right) = self.right {
                    right.get_mut(k)
                } else {
                    None
                }
            } else {
                if let Some(ref mut left) = self.left {
                    left.get_mut(k)
                } else {
                    None
                }
            }
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the tree.
    ///
    /// If the tree did not have this key present, `None` is returned.
    ///
    /// If the tree did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut tree = LLRB::new();
    /// assert_eq!(tree.insert(37, "a"), None);
    /// assert_eq!(tree.is_empty(), false);
    ///
    /// tree.insert(37, "b");
    /// assert_eq!(tree.insert(37, "c"), Some("b"));
    /// assert_eq!(tree[&37], "c");
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        if self.kv.is_none() {
            self.kv = Some((k, v));
            return None;
        }

        if is_red(&self.right) && is_red(&self.left) {
            self.color_flip();
        }

        let old = if let Some((ref key, ref mut val)) = self.kv {
            if key == &k {
                let old = mem::replace(val, v);
                Some(old)
            } else if &k < key {
                populate_insert(&mut self.left, k, v)
            } else {
                populate_insert(&mut self.right, k, v)
            }
        } else {
            None
        };

        if is_red(&self.right) {
            self.rotate_left();
        }

        if self.is_double_left_red() {
            self.rotate_right();
        }

        old
    }

    /// Removes a key from the tree, returning the value at the key if the key
    /// was previously in the tree.
    ///
    /// The key may be any borrowed form of the tree's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut tree = LLRB::new();
    /// tree.insert(1, "a");
    /// assert_eq!(tree.remove(&1), Some("a"));
    /// assert_eq!(tree.remove(&1), None);
    /// ```
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let mut old = None;
        let left_is_red = is_red(&self.left);
        let double_left_red = self.is_double_left_red();
        let right_is_red = is_red(&self.left);
        if let Some((ref mut key, ref mut val)) = self.kv {
            if k > key {
                if !left_is_red && !double_left_red {
                    // self.move_red_left();
                }
                if let Some(ref mut left) = self.left {
                    old = left.remove(k);
                }
            }
        }
        self.fix_up();
        old
    }

    fn min(&self) -> &LLRB<K, V> {
        self
    }

    /// Moves all elements from `other` into `Self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut a = LLRB::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    /// a.insert(3, "c");
    ///
    /// let mut b = LLRB::new();
    /// b.insert(3, "d");
    /// b.insert(4, "e");
    /// b.insert(5, "f");
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    /// assert_eq!(a[&3], "d");
    /// assert_eq!(a[&4], "e");
    /// assert_eq!(a[&5], "f");
    /// ```
    pub fn append(&mut self, other: &mut Self) {}

    /// Returns the number of elements in the tree.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut a = LLRB::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        // TODO store this in metadata encapsulating struct
        if self.kv.is_none() {
            0
        } else {
            let llen = if let Some(ref l) = self.left {
                l.len()
            } else {
                0
            };
            let rlen = if let Some(ref r) = self.right {
                r.len()
            } else {
                0
            };
            1 + llen + rlen
        }
    }

    /// Returns true if the tree contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use llrb::LLRB;
    ///
    /// let mut a = LLRB::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

fn is_red<K: Ord, V>(node: &Option<Box<LLRB<K, V>>>) -> bool {
    if let &Some(ref n) = node {
        if n.color == Color::Red {
            return true;
        }
    }
    false
}

fn populate_insert<K: Ord, V>(child_ref: &mut Option<Box<LLRB<K, V>>>, k: K, v: V) -> Option<V> {
    let mut child = child_ref.take().unwrap_or_else(|| Box::new(LLRB::default()));
    let ret = child.insert(k, v);
    *child_ref = Some(child);
    ret
}

#[cfg(test)]
mod tests {
    // TODO property: even black height

    // TODO property: never two reds in a row

    // TODO property: never right-leaning representation of 3-Node
}
