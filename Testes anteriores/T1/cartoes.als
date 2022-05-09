// Modelo abstracto de um sistema de emissão de cartões bancários

abstract sig Status {}
one sig Unissued, Issued, Cancelled extends Status {}

sig Card {
	var status : one Status
}

sig Client {
	var cards : set Card
}

// Algumas das propriedades desejadas para o sistema

assert NoUnissuedCards {
	// Os clientes nunca podem deter cartões unissued
	always (no Unissued & Client.cards.status)
}

assert NoSharedCards {
	// Ao longo da sua existência um cartão nunca pode pertencer a mais do que um cliente
	always (all c : Client, ca : c.cards | always cards.ca in c)
}

// Especifique as condições iniciais do sistema

fact Init {
	no cards
	Card.status = Unissued
}

// Especifique as operações do sistema por forma a garantir as propriedades
// de segurança

check NoUnissuedCards
check NoSharedCards

// Operação de emitir um cartão para um cliente
pred emit [c : Card, a : Client] {
	// guard
	historically c.status in Unissued
	// c not in Client.cards

	// effects
	c.status = Issued 
	cards' = cards + a -> c	

	// frame conditions
	all d : Card - c | d.status' = d.status
}

// Operação de cancelar um cartão
pred cancel [c : Card] {
	// guard
	c.status = Issued
	some cards.c

	// effects
	c.status' = Cancelled

	// frame conditions
	all d : Card - c | d.status' = d.status
}

pred nop {
	status' = status
	cards' = cards
}

fact Traces {
	always (nop or some c : Card | cancel[c] or some a : Client | emit[c,a])
}

// Especifique um cenário onde 3 cartões são emitidos a pelo menos 2
// clientes e são todos inevitavelmente cancelados, usando os scopes
// para controlar a cardinalidade das assinaturas
// Tente também definir um theme onde os cartões emitidos são verdes
// e os cancelados são vermelhos, ocultando depois toda a informação que
// seja redundante 
// Pode introduzir definições auxiliares no modelo se necessário

run Exemplo {
	eventually Card.status = Cancelled
} 
