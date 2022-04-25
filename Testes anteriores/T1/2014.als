abstract sig TYPE {}

one sig click, text, select extends TYPE {}

sig PARAMS {}

sig URL {}

sig Acao {
	tipo : one TYPE,
	params : set PARAMS,
	url : lone URL
}

sig TracoEx {
	init : one URL,
	traco : Int one -> Acao
}

fun acoesAlteracaoPagina [t : TracoEx] : set Acao {
	{a : (Int.(t.traco)) | one a.url}
}

fun primeiraAcao [t : TracoEx] : set Acao {
	{a : (Int.(t.traco)) | one a.url and a.url = t.init}
}

fact primeiraAcaoInit {
	all t : TracoEx | t.init = primeiraAcao[t].url
}

fun ultimaAcaoURL [t : TracoEx] : one URL {
	(ultimaAcao[t]).url
}

fun ultimaAcao [t : TracoEx] : set Acao {
	{a : Acao | all a2 : acoesAlteracaoPagina[t] | a in acoesAlteracaoPagina[t] and a != a2 and (t.traco).a > (t.traco).a2}
}

fact URLdiferentes {
	all disj a1, a2 : acoesAlteracaoPagina[TracoEx] | TracoEx.traco.a1 = TracoEx.traco.a2.minus[1] => a1.url != a2.url
}



run {} 
