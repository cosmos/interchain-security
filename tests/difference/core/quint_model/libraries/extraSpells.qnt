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

    // Returns the maximal element of the set.
    // If the set is empty, the function call will fail at runtime.
    pure def max(__set: Set[int]): int = maxBy(__set, __a => __a)

    run maxTest =
    all {
        assert(max(Set(1, 2, 3)) == 3),
    }

    // Returns the minimal element of the set.
    // If the set is empty, the function call will fail at runtime.
    pure def min(__set: Set[int]): int = minBy(__set, __a => __a)

    run minTest =
    all {
        assert(min(Set(1, 2, 3)) == 1),
    }

    pure def HasSubsequence(__this: List[a], __other: List[a]): bool = {
      if(__other.length() > __this.length()) {
        false
      } else {
        0.to(__this.length() - __other.length()) // go through all possible starting points of __other in __this
        .exists(
          __start => __this.slice(__start, __start + __other.length()) == __other
        )
      }
    }

    run HasSubsequenceTest =
    all {
      assert(List(1, 2, 3, 4).HasSubsequence(List(1, 2))),
      assert(List(1, 2, 3, 4).HasSubsequence(List(2, 3))),
      assert(List(1, 2, 3, 4).HasSubsequence(List(3, 4))),
      assert(List(1, 2, 3, 4).HasSubsequence(List(1, 2, 3))),
      assert(not(List(1, 2, 3, 4).HasSubsequence(List(1, 3)))),
      assert(not(List().HasSubsequence(List(1)))),
      assert(List().HasSubsequence(List())),
      assert(List(1).HasSubsequence(List())),
      assert(List(1).HasSubsequence(List(1))),
    }

    // Returns the maximum element of a set, according to a given function.
    // If two elements are equally large, an arbitrary one will be returned.
    // If the set is empty, the function call will fail at runtime.
    pure def maxBy(__set: Set[a], __f: a => int): a = {
      __set.fold(
        oneOf(__set),
        (__m, __e) => if(__f(__m) > __f(__e)) {__m } else {__e}
      )
    }

    run maxByTest =
    all {
      assert(maxBy(Set(1, 2, 3), __x => __x) == 3),
      assert(maxBy(Set(1, 2, 3), __x => -__x) == 1),
    }

    // Like maxBy, but returns the minimum element.
    pure def minBy(__set: Set[a], __f: a => int): a = {
      __set.fold(
        oneOf(__set),
        (__m, __e) => if(__f(__m) < __f(__e)) {__m } else {__e}
      )
    }
}
