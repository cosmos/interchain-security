
class KeyDelegation:
    def __init__(self):
        self.localKeyToLastUpdate = {}
        self.localKeyToCurrentForeignKey
        self.foreignKeyToLocalKey = {}
        self.foreignKeyToVSCIDWhenLastSent = {}
        self.localKeysForWhichUpdateMustBeSent = set()

    def SetKey(self, v, k):
        self.currentKey[v] = k
        if v in self.localKeyToLastUpdate:
            [_, lastPower] = self.localKeyToLastUpdate[v]
            if 0 < lastPower:
                # If validator is known to the consumer
                self.localKeysForWhichUpdateMustBeSent.add(v)

    def GetLocalKey(self, foreignKey):
        return self.foreignKeyToLocalKey[foreignKey]

    def ComputeUpdates(self, vscid, localUpdates):
        updates = {}
        # Ship updates for any
        for v in self.localKeysForWhichUpdateMustBeSent:
            currKey = self.localKeyToCurrentForeignKey[v]
            [lastKey, lastPower] = self.localKeyToLastUpdate[v]
            updates[lastKey] = 0
            updates[currKey] = lastPower
        self.localKeysForWhichUpdateMustBeSent = set()
        for v, power in localUpdates.items():  # Will happen if power changed since last block
            if v in self.localKeyToLastUpdate:
                [lastKey, _] = self.localKeyToLastUpdate[v]
                updates[lastKey] = 0
            currKey = self.localKeyToCurrentForeignKey[v]
            updates[currKey] = power

        for foreignKey, power in updates.items():
            self.foreignKeyToVSCIDWhenLastSent[foreignKey] = vscid
            self.localKeyToLastUpdate[self.foreignKeyToLocalKey[foreignKey]] = [
                foreignKey, power]
        return updates

    def Prune(self, mostRecentlyMaturedVscid):
        removed = [foreignKey for foreignKey,
                   vscid in self.foreignKeyToVSCIDWhenLastSent if vscid <= mostRecentlyMaturedVscid]
        for foreignKey in removed:
            del self.foreignKeyToVSCIDWhenLastSent[foreignKey]
            del self.foreignKeyToLocalKey[foreignKey]


consumers = ["c0", "c1"]
vals = ["v0", "v1"]


class Provider:
    def __init__(self):
        self.keyDelegations = {c: KeyDelegation() for c in consumers}
        pass

    def SendUpdates(self):
        for c in consumers:
            updates = {"v0": 42, "v1": 0}
            updates = self.keyDelegations[c].computeUpdates(updates)
            # ship the updates

    def SetKey(self, c, v, k):
        self.keyDelegations[c].SetKey(v, k)

    def Slash(self, c, foreignKey, vscID):
        localKey = self.keyDelegations[c].foreignKeyToLocalKey[foreignKey]
        # slash

    def Mature(self, c, ascendingVscids):
        latestVscid = ascendingVscids[-1]
        self.keyDelegations[c].Prune(latestVscid)


def main():
    print("hello")
    pass


if __name__ == "__main__":
    # x = {c: KeyDelegation() for c in consumers}
    # x["c0"].lastKeySent = {1: 2}
    # print(x["c0"].lastKeySent)
    # print(x["c1"].lastKeySent)
    main()
