sig Name {}

sig Pessoa {
	n : one Name,
	descendentes : set Pessoa
}

fact doisAscendentes {
	all p : Pessoa | #(descendentes.p) = 2
}

fun pessoaOrigem : Pessoa {
	{p : Pessoa | all pr : Pessoa - p | pr in p.^descendentes}
}

run {} for 6
