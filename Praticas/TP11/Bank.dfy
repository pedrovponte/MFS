/* 
* Formal specification and verification of a bank account.
* Used to illustration the verification of object-oriented programs and design by contract.
* Difficulty: Low.
* FEUP, M.EIC, MFS, 2021/22.
*/

class BankAccount {
    var balance: real;
    
    constructor (initialBalance: real)
    {
        balance := initialBalance;
    }
 
    function method getBalance() : real
    {
        balance
    }

    method deposit(amount : real)
    {
        balance := balance + amount;
    }

    method withdraw(amount : real)
    {
        balance := balance - amount;
    }

    method transfer(amount : real, destination: BankAccount)
    {
        this.balance := this.balance - amount;
        destination.balance:= destination.balance + amount;
    }
}

// A simple test case.
method testBankAccount()
{
    var a := new BankAccount(10.0);
    assert a.getBalance() == 10.0;

    var b := new BankAccount(0.0);
    assert b.getBalance() == 0.0;

    a.deposit(10.0);
    assert a.getBalance() == 20.0;

    a.withdraw(5.0);
    assert a.getBalance() == 15.0;

    a.transfer(15.0, b);
    assert a.getBalance() == 0.0;
    assert b.getBalance() == 15.0;
}