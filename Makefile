all: deflate

DeflateNotations.vo: DeflateNotations.v
	coqc DeflateNotations.v

Quicksort.vo: Quicksort.v DeflateNotations.vo
	coqc Quicksort.v

Lex.vo: Lex.v DeflateNotations.vo
	coqc Lex.v

Transports.vo: Transports.v DeflateNotations.vo
	coqc Transports.v

Prefix.vo: Prefix.v DeflateNotations.vo
	coqc Prefix.v

Repeat.vo: Repeat.v Prefix.vo Lex.vo Transports.vo DeflateNotations.vo
	coqc Repeat.v

Combi.vo: Combi.v Repeat.vo Prefix.vo Transports.vo Lex.vo Quicksort.vo DeflateNotations.vo
	coqc Combi.v

KraftList.vo: KraftList.v DeflateNotations.vo Prefix.vo Combi.vo
	coqc KraftList.v

KraftVec.vo: KraftVec.v KraftList.vo DeflateNotations.vo Prefix.vo Combi.vo Transports.vo
	coqc KraftVec.v

DeflateCoding.vo: DeflateCoding.v DeflateNotations.vo Quicksort.vo Lex.vo Transports.vo Prefix.vo Repeat.vo Combi.vo KraftList.vo KraftVec.vo
	coqc DeflateCoding.v

deflate: Quicksort.vo Lex.vo Transports.vo Prefix.vo Repeat.vo Combi.vo KraftList.vo KraftVec.vo DeflateCoding.vo
