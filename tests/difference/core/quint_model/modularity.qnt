module bank {
    var balances: str -> int

    action Send(sender: str, receiver: str, amt: int): bool = all {
        balances.get(sender) > amt,
        balances' = balances.set(sender, balances.get(sender) - amt),
    }

    action __bank_noop(): bool = all {
        balances' = balances,
    }
}

module governance {
    var votes: str -> bool

    action Vote(voter: str, vote: bool): bool = all {
        votes' = votes.set(voter, vote),
    }

    action __gov_noop(): bool = all {
        votes' = votes,
    }
}

module main {
    import bank.*
    import governance.*


   // working
   action MainAction(boolean: bool): bool = all {
        if(boolean) {
            all {
                Send("Alice", "Bob", 10),
                votes' = votes,
            }
        } else {
            all { 
                balances' = balances,
                Vote("Alice", true)
            }
        }
   }

   // not working
   action MainAction2(boolean: bool): bool = all {
        if(boolean) {
            all {
                Send("Alice", "Bob", 10),
                votes' = votes,
            }
        } else {
            all { 
                balances' = balances,
                Vote("Alice", true)
            }
        }
   }
}