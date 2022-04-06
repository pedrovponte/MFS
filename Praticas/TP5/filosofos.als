// Modelo do jantar dos filósofos

// As "coisas" à volta da mesa
abstract sig Coisa {
	prox : one Coisa
}

sig Filosofo extends Coisa {
	// Garfos que cada filósofo tem na mão
	var garfos : set Garfo
}

sig Garfo extends Coisa {}

// Especifique a configuração da mesa
fact Mesa {
	// A mesa é redonda, ou seja, as coisas formam um anel
	all c : Coisa | Coisa in c.^prox
	// Os garfos e os filósofos estão intercalados
	Garfo.prox in Filosofo
	Filosofo.prox in Garfo
}

// Especifique os seguintes eventos

// Um filosofo pode comer se já tiver os dois garfos junto a si
// e pousa os garfos depois
pred come [f : Filosofo] {
	// guarda
	some g1, g2 : f.garfos | g1 != g2
	// #(f.garfos) = 2

	// efeito
	// garfos' = garfos - f <: garfos
	no f.garfos'
	all f1 : Filosofo - f | f.garfos' = f.garfos
}

// Um filósofo pode pegar num dos garfos que estejam
// pousados junto a si
pred pega [f : Filosofo] {
	f.prox not in Filosofo.garfos or prox.f not in Filosofo.garfos 
}

// Para além de comer ou pegar em garfos os filósofos podem pensar
pred pensa [f : Filosofo] {
	garfos' = garfos
}

fact Comportamento {
	// No inicio os garfos estão todos pousados
	no garfos
	// Depois os filósfos só podem comer, pegar ou pensar
	always (some f : Filosofo | come[f] or pega[f] or pensa[f])
}

// Especifique as seguintes propriedades

assert GarfosNaMao {
	// O mesmo garfo nunca pode estar na mão de dois filósofos

}
check GarfosNaMao for 6

assert SempreQuePegaCome {
	// Qualquer filósofo que pega num garfo vai conseguir comer

}
check SempreQuePegaCome for 6

assert SemBloqueio {
	// O sistema não pode bloquear numa situação em que só é possível pensar

}
check SemBloqueio for 6

// Especifique um cenário com 4 filósofos onde todos conseguem comer
run Exemplo {

}
