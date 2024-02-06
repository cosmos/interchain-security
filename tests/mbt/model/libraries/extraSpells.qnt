// -*- mode: Bluespec; -*-

// This module is just a library with utility functions (sometimes called spells in Quint).
module extraSpells {

  pure def prepend(__list: List[a], __elem: a): List[a] = {
    List(__elem).concat(__list)
  }

  run prependTest = all {
    assert(List(2,3,4).prepend(1) == List(1,2,3,4)),
    assert(List().prepend(1) == List(1)),
  }

    /// An annotation for writing preconditions.
  /// - @param __cond condition to check
  /// - @returns true if and only if __cond evaluates to true
  pure def require(__cond: bool): bool = __cond

  run requireTest = all {
    assert(require(4 > 3)),
    assert(not(require(false))),
  }

  /// A convenience operator that returns a string error code,
  ///  if the condition does not hold true.
  ///
  /// - @param __cond condition to check
  /// - @param __error a non-empty error message
  /// - @returns "", when __cond holds true; otherwise __error
  pure def requires(__cond: bool, __error: str): str = {
    if (__cond) "" else __error
  }

  run requiresTest = all {
    assert(requires(4 > 3, "4 > 3") == ""),
    assert(requires(4 < 3, "false: 4 < 3") == "false: 4 < 3"),
  }

  /// Compute the absolute value of an integer
  ///
  /// - @param __i : an integer whose absolute value we are interested in
  /// - @returns |__i|, the absolute value of __i
  pure def abs(__i: int): int = {
    if (__i < 0) -__i else __i
  }

  run absTest = all {
    assert(abs(3) == 3),
    assert(abs(-3) == 3),
    assert(abs(0) == 0),
  }

  /// Remove a set element.
  ///
  /// - @param __set a set to remove an element from
  /// - @param __elem an element to remove
  /// - @returns a new set that contains all elements of __set but __elem
  pure def setRemove(__set: Set[a], __elem: a): Set[a] = {
    __set.exclude(Set(__elem))
  }

  run setRemoveTest = all {
    assert(Set(2, 4) == Set(2, 3, 4).setRemove(3)),
    assert(Set() == Set().setRemove(3)),
  }

  /// Test whether a key is present in a map
  ///
  /// - @param __map a map to query
  /// - @param __key the key to look for
  /// - @returns true if and only __map has an entry associated with __key
  pure def has(__map: a -> b, __key: a): bool = {
    __map.keys().contains(__key)
  }

  run hasTest = all {
    assert(Map(2 -> 3, 4 -> 5).has(2)),
    assert(not(Map(2 -> 3, 4 -> 5).has(6))),
  }

  /// Get the map value associated with a key, or the default,
  /// if the key is not present.
  ///
  /// - @param __map the map to query
  /// - @param __key the key to search for
  /// - @returns the value associated with the key, if __key is
  ///   present in the map, and __default otherwise
  pure def getOrElse(__map: a -> b, __key: a, __default: b): b = {
    if (__map.has(__key)) {
      __map.get(__key)
    } else {
      __default
    }
  }

  run getOrElseTest = all {
    assert(Map(2 -> 3, 4 -> 5).getOrElse(2, 0) == 3),
    assert(Map(2 -> 3, 4 -> 5).getOrElse(7, 11) == 11),
  }

  /// Remove a map entry.
  ///
  /// - @param __map a map to remove an entry from
  /// - @param __key the key of an entry to remove
  /// - @returns a new map that contains all entries of __map
  ///          that do not have the key __key
  pure def mapRemove(__map: a -> b, __key: a): a -> b = {
    __map.keys().setRemove(__key).mapBy(__k => __map.get(__k))
  }

  run mapRemoveTest = all {
    assert(Map(3 -> 4, 7 -> 8) == Map(3 -> 4, 5 -> 6, 7 -> 8).mapRemove(5)),
    assert(Map() == Map().mapRemove(3)),
  }

    /// Removes a set of map entry.
    ///
    /// - @param __map a map to remove an entry from
    /// - @param __keys a set of keys to remove from the map
    /// - @returns a new map that contains all entries of __map
    ///          that do not have a key in __keys
    pure def mapRemoveAll(__map: a -> b, __keys: Set[a]): a -> b = {
        __map.keys().exclude(__keys).mapBy(__k => __map.get(__k))
    }

    run mapRemoveAllTest =
        val m = Map(3 -> 4, 5 -> 6, 7 -> 8)
        all {
            assert(m.mapRemoveAll(Set(5, 7)) == Map(3 -> 4)),
            assert(m.mapRemoveAll(Set(5, 99999)) == Map(3 -> 4, 7 -> 8)),
        }

    //// Returns a list of all elements of a set.
    ////
    //// - @param __set a set
    //// - @returns a list of all elements of __set
    pure def toList(__set: Set[a]): List[a] = {
        __set.fold(List(), (__l, __e) => __l.append(__e))
    }

  /// The type of orderings between comparable things
  // Follows https://hackage.haskell.org/package/base-4.19.0.0/docs/Data-Ord.html#t:Ordering
  // and we think there are likely benefits to using 3 constant values rather than the more
  // common integer range in Apalache.
  type Ordering =
    | EQ
    | LT
    | GT

  /// Comparison of integers
  pure def intCompare(__a: int, __b:int): Ordering = {
    if (__a < __b)
      { LT }
    else if (__a > __b)
      { GT }
    else
      { EQ }
  }

  /// Assuming `__l` is sorted according to `__cmp`, returns a list with the element `__x`
  /// insterted in order.
  ///
  /// If `__l` is not sorted, `__x` will be inserted after the first element less than
  /// or equal to it.
  ///
  /// - @param __l a sorted list
  /// - @param __x an element to be inserted
  /// - @param __cmp an operator defining an `Ordering` of the elemnts of type `a`
  /// - @returns a sorted list that includes `__x`
  pure def sortedListInsert(__l: List[a], __x: a, __cmp: (a, a) => Ordering): List[a] = {
    // We need to track whether __x has been inserted, and the accumulator for the new list
    val __init = { is_inserted: false, acc: List() }

    val __result = __l.foldl(__init, (__state, __y) =>
      if (__state.is_inserted)
        { ...__state, acc: __state.acc.append(__y) }
      else
        match __cmp(__x, __y) {
          | GT => { ...__state, acc: __state.acc.append(__y) }
          | _  => { is_inserted: true, acc: __state.acc.append(__x).append(__y)  }
        })

    if (not(__result.is_inserted))
      // If __x was not inserted, it was GT than every other element, so it goes at the end
      __result.acc.append(__x)
    else
      __result.acc
  }

  run sortedListInsertTest = all {
    assert(List().sortedListInsert(3, intCompare) == List(3)),
    assert(List(1,2,4).sortedListInsert(3, intCompare) == List(1,2,3,4)),
    assert(List(4,1,2).sortedListInsert(3, intCompare) == List(3,4,1,2)),
    assert(List(1,2,3).sortedListInsert(4, intCompare) == List(1,2,3,4)),
  }

  //// Returns a list of all elements of a set.
  //// The ordering will be arbitrary.
  ////
  //// - @param __set a set
  //// - @param __cmp an ordering over the elements of the set
  //// - @returns a sorted list of all elements of __set
  pure def toSortedList(__set: Set[a], __cmp: (a, a) => Ordering): List[a] = {
      __set.fold(List(), (__l, __e) => __l.sortedListInsert(__e, __cmp))
  }

    //// Returns a set of the elements in the list.
    ////
    //// - @param __list a list
    //// - @returns a set of the elements in __list
    pure def toSet(__list: List[a]): Set[a] = {
        __list.foldl(Set(), (__s, __e) => __s.union(Set(__e)))
    }

    run toListAndSetTest =
    all {
        assert(Set(3, 2, 1).toList().toSet() == Set(1, 2, 3)),
        assert(List(2,3,1).toSet() == Set(1, 2, 3)),
        assert(List(2,3,1).toSet() == List(3,2,1).toSet()),
        assert(toList(Set()) == List()),
        assert(toSet(List()) == Set())
    }

    pure def add(__set: Set[a], elem: a): Set[a] = {
        __set.union(Set(elem))
    }

    pure def values(__map: a -> b): Set[b] = {
        __map.keys().fold(Set(), (__s, __k) => __s.add(__map.get(__k)))
    }
    run valuesTest =
    all {
        assert(values(Map(1 -> 2, 3 -> 4)) == Set(2, 4)),
        assert(values(Map()) == Set())
    }

    //// Returns a new list l, where l[i] = __f(__list[i])
    ////
    //// - @param __list a list
    //// - @param __f a function that is applied to each element of __list
    ////
    //// - @returns a set of the elements in __list
    pure def transform(__list: List[a], __f: a => b): List[b] = {
        __list.foldl(List(), (__l, __e) => __l.append(__f(__e)))
    }

    run transformTest =
    all {
        assert(transform(List(1, 2, 3), __x => __x + 1) == List(2, 3, 4)),
        assert(transform(List(), __x => __x + 1) == List()),
        assert(transform(List(1, 2, 3), __x => __x * 2) == List(2, 4, 6)),
        assert(transform(List(1, 2, 3), __x => __x) == List(1, 2, 3)),
    }


    // listForAll returns true if the given predicate function returns true for all elements in the given list,
    // and false otherwise.
    //
    // Parameters:
    // - __list: The list to check.
    // - __f: The predicate function to apply to each element in the list.
    //
    // Returns:
    // - true if the predicate function returns true for all elements in the list, and false otherwise.
    pure def listForAll(__list: List[a], __f: a => bool): bool = {
        __list.foldl(true, (__b, __e) => __b and __f(__e))
    }

    run listForAllTest =
    all {
        assert(listForAll(List(1, 2, 3), __x => __x > 0)),
        assert(not(listForAll(List(1, 2, 3), __x => __x > 1))),
        assert(listForAll(List(), __x => __x > 0)),
    }

  /// Compute the sum of the values over all entries in a map.
  ///
  /// - @param myMap a map from keys to integers
  /// - @returns the sum; when the map is empty, the sum is 0.
  pure def mapValuesSum(myMap: a -> int): int = {
    myMap.keys().fold(0, ((sum, i) => sum + myMap.get(i)))
  }

  run mapValuesSumTest = all {
    assert(Map().mapValuesSum() == 0),
    assert(2.to(5).mapBy(i => i * 2).mapValuesSum() == 28),
    assert(Map(2 -> -4, 4 -> 2).mapValuesSum() == -2),
  }

  /// Returns a map of a subset of keys and values from a map,
  // where only those keys are included for which the given __f
  // returns true.
  pure def mapFilter(__map: a -> b, __f: a => bool): a -> b = {
    __map.keys().filter(e => __f(e)).mapBy(__k => __map.get(__k))
  }

  /// Compute the maximum of two integers.
  ///
  /// - @param __i first integer
  /// - @param __j second integer
  /// - @returns the maximum of __i and __j
  pure def max(__i: int, __j: int): int = {
    if (__i > __j) __i else __j
  }

  run maxTest = all {
    assert(max(3, 4) == 4),
    assert(max(6, 3) == 6),
    assert(max(10, 10) == 10),
    assert(max(-3, -5) == -3),
    assert(max(-5, -3) == -3),
  }

  /// Compute the minimum of two integers.
  ///
  /// - @param __i first integer
  /// - @param __j second integer
  /// - @returns the minimum of __i and __j
  pure def min(__i: int, __j: int): int = {
    if (__i < __j) __i else __j
  }

  run minTest = all {
    assert(min(3, 4) == 3),
    assert(min(6, 3) == 3),
    assert(min(10, 10) == 10),
    assert(min(-3, -5) == -5),
    assert(min(-5, -3) == -5),
  }
}