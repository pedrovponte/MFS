sig Institution {}

sig Researcher {
	affiliation : set Institution
}

sig Title {}

sig Paper {
	title : Title,
	authors : some Researcher
}

sig Conference {
	pcMembers : set Researcher, -- program committee members
	papers : set Paper, -- papers submitted
	reviewers : papers -> pcMembers -- reviewers assigned to papers
} {
	-- C1: it is not possible to have two different papers with the same title


	-- C2: Authors cannot be reviewers (i.e., a paper cannot be assigned for review
	-- to a researcher that is also an author of the paper)


	-- C3: reviewers cannot be affiliated with the same institution as the authors
	-- (i.e., a paper cannot be assigned for review to a researcher that is affiliated
	-- with the same institution as one of the authors)


}

-- Example

one sig I1, I2 extends Institution {}

one sig R1 extends Researcher {}

one sig R2 extends Researcher {} {affiliation = I1}

one sig R3, R4 extends Researcher {} {affiliation = I2}

one sig T1, T2 extends Title {}

one sig P1 extends Paper {} {title = T1 && authors = R2}

one sig P2 extends Paper {} {title = T2 && authors = R3 + R4}

one sig TestConf extends Conference {} {
	pcMembers = R1 + R2 + R4
	papers = P1 + P2
	reviewers = P1 -> (R1 + R4) + P2 -> (R1 + R2)
}
