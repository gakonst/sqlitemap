//! # SQLiteMap
//!
//! A Rust port of python's [Sqlitedict](https://github.com/RaRe-Technologies/sqlitedict).
//! Exposes a HashMap-like interface using [`rusqlite`](https://docs.rs/rusqlite)

use rusqlite::{types::FromSql, Connection, Error as SqliteError, ToSql, NO_PARAMS};
use std::borrow::Borrow;
use std::marker::PhantomData;
use std::path::Path;

/// A key-value store using Sqlite3 as a backend, following [`HashMap`]'s interface.
///
/// [`HashMap`]: std::collections::HashMap
pub struct SqliteMap<K, V> {
    connection: Connection,
    table_name: String,
    key: PhantomData<K>,
    value: PhantomData<V>,
}

type Result<T> = std::result::Result<T, SqliteError>;

impl<K: FromSql + ToSql, V: ToSql + FromSql> SqliteMap<K, V> {
    /// Creates a new Sqlite connection to the provided database file with the specified
    /// table name
    pub fn new<P: AsRef<Path>>(fname: P, table_name: &str) -> Result<Self> {
        let connection = Connection::open(fname)?;
        Self::from_connection(connection, table_name)
    }

    /// Creates a new in-memory Sqliteconnection file with the specified
    /// table name
    pub fn in_memory(table_name: &str) -> Result<Self> {
        let connection = Connection::open_in_memory()?;
        Self::from_connection(connection, table_name)
    }

    /// Connects to an already opened [`Connection`] with the specified table name
    ///
    /// [`Connection`]: https://docs.rs/rusqlite/0.24.1/rusqlite/struct.Connection.html
    pub fn from_connection(connection: Connection, table_name: &str) -> Result<Self> {
        connection.execute_batch(&format!(
            "CREATE TABLE IF NOT EXISTS {} (key BLOB PRIMARY KEY, value BLOB)",
            table_name
        ))?;

        Ok(Self {
            connection,
            table_name: table_name.to_owned(),
            key: PhantomData,
            value: PhantomData,
        })
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [module-level documentation]: crate::collections#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() -> Result<(), Box<dyn std::error::Error>> {
    /// use sqlitemap::SqliteMap;
    ///
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// assert_eq!(map.insert(37, "a".to_owned())?, None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b".to_owned());
    /// assert_eq!(map.insert(37, "c".to_owned())?, Some("b".to_owned()));
    /// # Ok(())
    /// # }
    /// ```
    pub fn insert(&self, key: K, value: V) -> Result<Option<V>> {
        // Can we do this in a more performant way instead of doing
        // 2 queries?
        let ret = self.get(&key)?;
        let res = self.connection.execute(
            &format!("REPLACE INTO {} (key, value) VALUES (?,?)", self.table_name),
            &[key.to_sql()?, value.to_sql()?],
        )?;
        // must always change 1 row
        debug_assert_eq!(res, 1);
        Ok(ret)
    }

    #[inline]
    /// Returns the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() -> Result<(), Box<dyn std::error::Error>> {
    /// use sqlitemap::SqliteMap;
    ///
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// map.insert(1, "a".to_owned());
    /// assert_eq!(map.get(&1)?, Some("a".to_owned()));
    /// assert_eq!(map.get(&2)?, None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Result<Option<V>>
    where
        K: Borrow<Q>,
        Q: ?Sized + ToSql,
    {
        let res = self.connection.query_row(
            &format!("SELECT value FROM {} WHERE key = ?", self.table_name),
            &[key.borrow().to_sql()?],
            |row| row.get(0),
        );

        match res {
            Ok(res) => Ok(Some(res)),
            Err(err) => match err {
                SqliteError::QueryReturnedNoRows => Ok(None),
                _ => Err(err.into()),
            },
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// use sqlitemap::SqliteMap;
    ///
    /// # fn foo() -> Result<(), Box<dyn std::error::Error>> {
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// map.insert(1, "a".to_owned());
    /// assert_eq!(map.contains_key(&1)?, true);
    /// assert_eq!(map.contains_key(&2)?, false);
    /// # Ok(())
    /// # }
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: ?Sized + ToSql,
    {
        let res: std::result::Result<K, _> = self.connection.query_row(
            &format!("SELECT 1 FROM {} WHERE key = ?", self.table_name),
            &[key.borrow().to_sql()?],
            |row| row.get(0),
        );

        match res {
            Ok(_) => Ok(true),
            Err(err) => match err {
                SqliteError::QueryReturnedNoRows => Ok(false),
                _ => Err(err.into()),
            },
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() -> Result<(), Box<dyn std::error::Error>> {
    /// use sqlitemap::SqliteMap;
    ///
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// map.insert(1, "a".to_owned());
    /// assert_eq!(map.remove(&1)?, Some("a".to_owned()));
    /// assert_eq!(map.remove(&1)?, None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn remove<Q>(&self, key: &Q) -> Result<Option<V>>
    where
        K: Borrow<Q>,
        Q: ?Sized + ToSql,
    {
        let ret = self.get(&key)?;

        self.connection.execute(
            &format!("DELETE FROM {} WHERE key = ?", self.table_name),
            &[key.to_sql()?],
        )?;

        Ok(ret)
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use sqlitemap::SqliteMap;
    ///
    /// let mut a = SqliteMap::in_memory("test").unwrap();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a".to_owned());
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let res: isize = self
            .connection
            .query_row(
                &format!("SELECT COUNT(*) FROM {}", self.table_name),
                NO_PARAMS,
                |row| row.get(0),
            )
            .expect("length query should never fail");
        res as usize
    }

    #[inline]
    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use sqlitemap::SqliteMap;
    ///
    /// let a = SqliteMap::in_memory("test").unwrap();
    /// assert!(a.is_empty());
    /// a.insert(1, "a".to_owned());
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use sqlitemap::SqliteMap;
    ///
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// map.insert("a".to_owned(), 1);
    /// map.insert("b".to_owned(), 2);
    /// map.insert("c".to_owned(), 3);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.into()
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use sqlitemap::SqliteMap;
    ///
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// map.insert("a".to_owned(), 1);
    /// map.insert("b".to_owned(), 2);
    /// map.insert("c".to_owned(), 3);
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use sqlitemap::SqliteMap;
    ///
    /// let map = SqliteMap::in_memory("test").unwrap();
    /// map.insert("a".to_owned(), 1);
    /// map.insert("b".to_owned(), 2);
    /// map.insert("c".to_owned(), 3);
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }
}

/// An iterator over the entries of a [`SqliteMap`].
///
/// This `struct` is created by the [`iter`] method on [`SqliteMap`]. See its
/// documentation for more.
///
/// [`iter`]: SqliteMap::iter
/// [`SqliteMap`]: SqliteMap
pub struct Iter<'a, K, V> {
    inner: &'a SqliteMap<K, V>,
    idx: usize,
}

/// An iterator over the keys of a [`SqliteMap`].
///
/// This `struct` is created by the [`keys`] method on [`SqliteMap`]. See its
/// documentation for more.
///
/// [`keys`]: SqliteMap::keys
/// [`SqliteMap`]: SqliteMap
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

/// An iterator over the values of a [`SqliteMap`].
///
/// This `struct` is created by the [`values`] method on [`SqliteMap`]. See its
/// documentation for more.
///
/// [`values`]: SqliteMap::values
/// [`SqliteMap`]: SqliteMap
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> From<&'a SqliteMap<K, V>> for Iter<'a, K, V>
where
    K: FromSql + ToSql,
    V: ToSql + FromSql,
{
    fn from(inner: &'a SqliteMap<K, V>) -> Self {
        Self { inner, idx: 0 }
    }
}

impl<'a, K, V> IntoIterator for &'a SqliteMap<K, V>
where
    K: FromSql + ToSql + Clone,
    V: ToSql + FromSql + Clone,
{
    type Item = (K, V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V>
where
    K: FromSql + ToSql + Clone,
    V: FromSql + ToSql + Clone,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V>
where
    K: FromSql + ToSql + Clone,
    V: FromSql + ToSql + Clone,
{
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: FromSql + ToSql + Clone,
    V: FromSql + ToSql + Clone,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let mut stmt = self
            .inner
            .connection
            .prepare(&format!(
                "SELECT * FROM {} ORDER BY rowid",
                self.inner.table_name
            ))
            .expect("could not prepare command");

        // Executes the query and gets the item
        let item = stmt
            .query_map(NO_PARAMS, |row| Ok((row.get(0)?, row.get(1)?)))
            .expect("could not get Key-Value iterator")
            .map(|item| item.expect("could not get k-v pair"))
            .nth(self.idx);
        self.idx += 1;
        item
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert() {
        let m = SqliteMap::in_memory("test").unwrap();
        assert_eq!(m.len(), 0);

        assert!(m.insert(1, 2).unwrap().is_none());
        assert_eq!(m.len(), 1);

        assert!(m.insert(2, 4).unwrap().is_none());
        assert_eq!(m.len(), 2);

        assert_eq!(m.get(&1).unwrap().unwrap(), 2);
        assert_eq!(m.get(&2).unwrap().unwrap(), 4);
        assert!(m.get(&3).unwrap().is_none());
    }

    #[test]
    fn test_remove() {
        let m = SqliteMap::in_memory("test").unwrap();
        assert!(m.insert(1, 2).unwrap().is_none());
        assert_eq!(m.remove(&1).unwrap(), Some(2));
        assert_eq!(m.remove(&1).unwrap(), None);
    }

    #[test]
    fn test_insert_overwrite() {
        let m = SqliteMap::in_memory("test").unwrap();
        assert!(m.insert(1, 2).unwrap().is_none());
        assert_eq!(m.get(&1).unwrap().unwrap(), 2);
        assert!(!m.insert(1, 3).unwrap().is_none());
        assert_eq!(m.get(&1).unwrap().unwrap(), 3);
    }

    #[test]
    fn test_insert_conflicts() {
        let m = SqliteMap::in_memory("test").unwrap();
        assert!(m.insert(1, 2).unwrap().is_none());
        assert!(m.insert(5, 3).unwrap().is_none());
        assert!(m.insert(9, 4).unwrap().is_none());
        assert_eq!(m.get(&9).unwrap().unwrap(), 4);
        assert_eq!(m.get(&5).unwrap().unwrap(), 3);
        assert_eq!(m.get(&1).unwrap().unwrap(), 2);
    }

    #[test]
    fn test_conflict_remove() {
        let m = SqliteMap::in_memory("test").unwrap();
        assert!(m.insert(1, 2).unwrap().is_none());
        assert_eq!(m.get(&1).unwrap().unwrap(), 2);
        assert!(m.insert(5, 3).unwrap().is_none());
        assert_eq!(m.get(&1).unwrap().unwrap(), 2);
        assert_eq!(m.get(&5).unwrap().unwrap(), 3);
        assert!(m.insert(9, 4).unwrap().is_none());
        assert_eq!(m.get(&1).unwrap().unwrap(), 2);
        assert_eq!(m.get(&5).unwrap().unwrap(), 3);
        assert_eq!(m.get(&9).unwrap().unwrap(), 4);
        assert!(m.remove(&1).unwrap().is_some());
        assert_eq!(m.get(&9).unwrap().unwrap(), 4);
        assert_eq!(m.get(&5).unwrap().unwrap(), 3);
    }

    #[test]
    fn test_iterate() {
        let m = SqliteMap::in_memory("test").unwrap();
        for i in 0..32 {
            assert!(m.insert(i, i * 2).unwrap().is_none());
        }
        assert_eq!(m.len(), 32);

        let mut observed: u32 = 0;

        // todo make refs
        for (k, v) in &m {
            assert_eq!(v, k * 2);
            observed |= 1 << k;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    fn from_iter<K, V, T>(iter: T) -> SqliteMap<K, V>
    where
        T: IntoIterator<Item = (K, V)>,
        K: FromSql + ToSql + Clone,
        V: ToSql + FromSql + Clone,
    {
        let m = SqliteMap::in_memory("test").unwrap();
        for (key, value) in iter.into_iter() {
            m.insert(key, value).unwrap();
        }
        m
    }

    #[test]
    fn test_keys() {
        let vec = vec![
            (1isize, "a".to_owned()),
            (2, "b".to_owned()),
            (3, "c".to_owned()),
        ];
        let map = from_iter(vec);
        assert!(map.contains_key(&1).unwrap());
        assert!(map.contains_key(&2).unwrap());
        assert!(map.contains_key(&3).unwrap());
        let keys: Vec<_> = map.keys().collect();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_values() {
        let vec = vec![
            (1, "a".to_owned()),
            (2, "b".to_owned()),
            (3, "c".to_owned()),
        ];
        let map = from_iter(vec);
        let values: Vec<_> = map.values().collect();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&"a".to_owned()));
        assert!(values.contains(&"b".to_owned()));
        assert!(values.contains(&"c".to_owned()));
    }

    #[test]
    #[ignore]
    fn test_lots_of_insertions() {
        let m = SqliteMap::in_memory("test").unwrap();

        for _ in 0..10 {
            assert!(m.is_empty());

            for i in 1..1001 {
                assert!(m.insert(i, i).unwrap().is_none());

                for j in 1..=i {
                    let r = m.get(&j).unwrap();
                    assert_eq!(r, Some(j));
                }

                for j in i + 1..1001 {
                    let r = m.get(&j).unwrap();
                    assert_eq!(r, None);
                }
            }

            for i in 1001..2001 {
                assert!(!m.contains_key(&i).unwrap());
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove(&i).unwrap().is_some());

                for j in 1..=i {
                    assert!(!m.contains_key(&j).unwrap());
                }

                for j in i + 1..1001 {
                    assert!(m.contains_key(&j).unwrap());
                }
            }

            for i in 1..1001 {
                assert!(!m.contains_key(&i).unwrap());
            }

            for i in 1..1001 {
                assert!(m.insert(i, i).unwrap().is_none());
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove(&i).unwrap().is_some());

                for j in i..1001 {
                    assert!(!m.contains_key(&j).unwrap());
                }

                for j in 1..i {
                    assert!(m.contains_key(&j).unwrap());
                }
            }
        }
    }
}
