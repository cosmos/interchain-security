import bisect

from .constants import *


class PartialOrder:
    def __init__(self):
        self.greatest_predecessor = {P: {}, C: {}}
        self.least_successor = {P: {}, C: {}}

    def deliver(self, receiving_chain, send_height, receive_height):

        h = send_height

        if receive_height in self.greatest_predecessor[receiving_chain]:
            h = max(self.greatest_predecessor[receiving_chain][receive_height], h)
        self.greatest_predecessor[receiving_chain][receive_height] = h

        sending_chain = {P: C, C: P}[receiving_chain]

        h = receive_height

        if send_height in self.least_successor[sending_chain]:
            h = min(self.least_successor[sending_chain][send_height], h)
        self.least_successor[sending_chain][send_height] = h

    def get_greatest_predecessor(self, chain, height):
        # If the greatest predecessor is not recorded
        # it is that of the greatest h, h < height, known
        heights = sorted(self.greatest_predecessor[chain].keys())
        i = bisect.bisect_right(heights, height)
        if i < 1:
            return None
        return self.greatest_predecessor[chain][heights[i - 1]]

    def get_least_successor(self, chain, height):
        # If the least successor is not recorded
        # it is that of the least h, height < h, known
        heights = sorted(self.least_successor[chain].keys())
        i = bisect.bisect_left(heights, height)
        if len(heights) <= i:
            return None
        return self.least_successor[chain][heights[i]]


class Blocks:
    class Block:
        def __init__(self, h, t, snapshot):
            self.h = h
            self.t = t
            self.snapshot = snapshot

    def __init__(self):
        self.partial_order = PartialOrder()
        # Inner dictionaries map heights to block data
        self.blocks = {P: {}, C: {}}

    def commit_block(self, chain, snapshot):
        h = snapshot.h[chain]
        t = snapshot.t[chain]
        assert h not in self.blocks[chain]
        self.blocks[chain][h] = Blocks.Block(h, t, snapshot)
