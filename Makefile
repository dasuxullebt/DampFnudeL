HashTable.vo: HashTable.v
	coqc HashTable.v

Intervals.vo: Intervals.v
	coqc Intervals.v

LSB.vo: LSB.v Transports.vo Shorthand.vo Combi.vo
	coqc LSB.v

EncodingRelation.vo: EncodingRelation.v Shorthand.vo DeflateCoding.vo  KraftVec.vo KraftList.vo Combi.vo Transports.vo Prefix.vo LSB.vo Repeat.vo Backreferences.vo StrongDec.vo
	coqc EncodingRelation.v

DecompressWithRecursiveSlowdown.vo : DecompressWithRecursiveSlowdown.v EncodingRelation.vo EncodingRelationProperties.vo Shorthand.vo Backreferences.vo Combi.vo
	coqc DecompressWithRecursiveSlowdown.v

Compress.vo : Compress.v Intervals.vo Prefix.vo HashTable.vo Shorthand.vo Backreferences.vo EncodingRelation.vo LSB.vo Combi.vo DeflateCoding.vo
	coqc Compress.v

EncodingRelationProperties.vo : EncodingRelationProperties.v Shorthand.vo DeflateCoding.vo KraftVec.vo KraftList.vo Combi.vo Transports.vo Prefix.vo LSB.vo Repeat.vo Backreferences.vo StrongDec.vo EncodingRelation.vo
	coqc EncodingRelationProperties.v

Backreferences.vo : Backreferences.v Combi.vo Shorthand.vo LSB.vo
	coqc Backreferences.v

Quicksort.vo: Quicksort.v
	coqc Quicksort.v

Lex.vo: Lex.v Shorthand.vo
	coqc Lex.v

Shorthand.vo: Shorthand.v
	coqc Shorthand.v

Transports.vo: Transports.v Shorthand.vo
	coqc Transports.v

Prefix.vo: Prefix.v Shorthand.vo
	coqc Prefix.v

Repeat.vo: Repeat.v Prefix.vo Lex.vo Shorthand.vo
	coqc Repeat.v

Combi.vo: Combi.v Repeat.vo Prefix.vo Transports.vo Lex.vo Shorthand.vo
	coqc Combi.v

KraftList.vo: KraftList.v Shorthand.vo Prefix.vo Combi.vo
	coqc KraftList.v

KraftVec.vo: KraftVec.v KraftList.vo Shorthand.vo Prefix.vo Combi.vo Transports.vo
	coqc KraftVec.v

StrongDec.vo: StrongDec.v Shorthand.vo Prefix.vo Combi.vo
	coqc StrongDec.v

DeflateCoding.vo: DeflateCoding.v Shorthand.vo Quicksort.vo Lex.vo Transports.vo Prefix.vo Repeat.vo Combi.vo KraftList.vo KraftVec.vo StrongDec.vo
	coqc DeflateCoding.v

clean:
	rm -f *.vo *~ *.glob \#* Test.hs *.o TestCases *.hi
