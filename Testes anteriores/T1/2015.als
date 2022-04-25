sig Account {}

abstract sig Transaction { amount : Int}

sig Deposit, Withdrawal extends Transaction {} -- a transaction is either a deposit or a withdrawal

sig Client {
	accounts : some Account, -- a client can access several accounts (1 or more)
	withdrawalPrivileges : set Account, -- but can't withdraw from all of them (0..*)
	balance : Account set -> one Int, -- the amount each account currently has
	transactions : Account one  -> set Transaction -- a list of all account movements
}

pred invariants [c : Client] {
	-- the balance of an account should never be lower than 0
	all a : Account.balance | a >= 0
	
	-- a client can only withdraw from accounts she has access to
	withdrawalPrivileges in accounts

	-- a client only has balance from accounts she has access to
	balance.Int in accounts
}

-- transaction t withdraws quantity q from account a of a client c,
-- resulting in a new state cf
pred withdraw [c, cf : Client, a : Account, qty : Int, t : Transaction] {
	-- pre-conditions (without using predicate invariants)
	a in c.accounts
	a in c.withdrawalPrivileges
	a.(c.balance) >= qty
	qty > 0
	
	-- post-conditions (without using predicate invariants)
	a in cf.accounts
	a in cf.withdrawalPrivileges
	a.(cf.balance) = a.(c.balance).minus[qty]
	a.(cf.balance) >= 0
	cf.transactions = c.transactions + a -> t
}

-- gives the total balance of a client c
fun totalBalance [c : Client] : Int {
	sum a : c.accounts | a.(c.balance)
}

assert withdraw_preserves_invariants {
	all c, cf : Client, account : Account, qty : Int, t : Transaction |
	-- if one withdraws from a consistent client
	(invariants [c] and withdraw [c, cf, account, qty, t]) =>
	-- one ends up with a new consistent client state
	(invariants [cf])
}

check withdraw_preserves_invariants

run {} for 6
