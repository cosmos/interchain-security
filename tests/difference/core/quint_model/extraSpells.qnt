module extraSpells {

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
        
    pure def listSorted(__list: List[a], __lt: (a, a) => bool): List[a] = {
    pure def __countSmaller(__j: int): int = {
      pure val __jth = __list[__j]
      __list.indices().filter(__i =>
        __lt(__list[__i], __jth) or (__list[__i] == __jth and __i < __j)
      )
      .size()
    }

    pure val __permutation = __list.indices().mapBy(__i => __countSmaller(__i))
        __list.foldl([], (__l, __i) => __l.append(__list[__permutation.get(__i)]))
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

}