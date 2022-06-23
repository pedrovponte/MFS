# Test 2 - Moodle

## 1

Which of the following Hoare triples is FALSE?

Selecione uma opção:

    a. {true} if x ≥ 0 then y := 1 else y := -1 {x * y ≥ 0}
    b. {i < 0} while i < 0 do i := i + 1 {i = 0}
    c. {x > 1} x := x - 1 {x > 0}
    d. I don't want to answer this question.
    **e. {true} skip {false}**

## 2

Which of the following Hoare triples is TRUE?

Selecione uma opção:

    a. {true} z := x; y := z - 1 {y > x}
    b. {true} y := x; y := x + x + y {y > x}
    c. {true} z := 1; y := x - z {x < y}
    d. I don't want to answer this question.
    e. {y < 0} x := x + y; y := x - y {y > x}

## 3

Which of the following expressions gives the weakest precondition of the following Hoare triple?

{wp} while r >= d do r := r - d {0 ≤ r ∧ r < d}

Selecione uma opção:

    a. d > 0
    b. r >= 0 ∧ d > 0
    c. I don't want to answer this question.
    d. r >= 0
    e. r >= 0 \/ d > 0
