Backreferences.vo: Backreferences.v Combi.vo Shorthand.vo LSB.vo Repeat.vo 
	coqc Backreferences.v
Combi.vo: Combi.v Shorthand.vo Lex.vo Prefix.vo Repeat.vo Transports.vo 
	coqc Combi.v
CpdtTactics.vo: CpdtTactics.v 
	coqc CpdtTactics.v
DecompressWithPheap.vo: DecompressWithPheap.v StrongDec.vo Shorthand.vo Combi.vo Repeat.vo Pheap.vo Backreferences.vo LSB.vo 
	coqc DecompressWithPheap.v
DeflateCoding.vo: DeflateCoding.v Shorthand.vo Quicksort.vo Lex.vo Transports.vo Prefix.vo Repeat.vo Combi.vo KraftList.vo KraftVec.vo StrongDec.vo 
	coqc DeflateCoding.v
EncodingRelationProperties2.vo: EncodingRelationProperties2.v StrongDec.vo EncodingRelation.vo EncodingRelationProperties.vo Shorthand.vo Combi.vo DeflateCoding.vo LSB.vo 
	coqc EncodingRelationProperties2.v
EncodingRelationProperties.vo: EncodingRelationProperties.v CpdtTactics.vo Shorthand.vo DeflateCoding.vo KraftVec.vo KraftList.vo Combi.vo Transports.vo Prefix.vo LSB.vo Repeat.vo Backreferences.vo StrongDec.vo EncodingRelation.vo 
	coqc EncodingRelationProperties.v
EncodingRelation.vo: EncodingRelation.v Shorthand.vo DeflateCoding.vo KraftVec.vo KraftList.vo Combi.vo Transports.vo Prefix.vo LSB.vo Repeat.vo Backreferences.vo StrongDec.vo 
	coqc EncodingRelation.v
Extraction.vo: Extraction.v Shorthand.vo 
	coqc Extraction.v
HashTable.vo: HashTable.v 
	coqc HashTable.v
Intervals.vo: Intervals.v Shorthand.vo 
	coqc Intervals.v
KraftList.vo: KraftList.v Shorthand.vo Prefix.vo Combi.vo 
	coqc KraftList.v
KraftVec.vo: KraftVec.v Shorthand.vo Prefix.vo Combi.vo KraftList.vo Transports.vo 
	coqc KraftVec.v
Lex.vo: Lex.v Shorthand.vo 
	coqc Lex.v
LSB.vo: LSB.v Transports.vo Shorthand.vo Combi.vo 
	coqc LSB.v
Pheap.vo: Pheap.v Combi.vo 
	coqc Pheap.v
Prefix.vo: Prefix.v Shorthand.vo 
	coqc Prefix.v
Quicksort.vo: Quicksort.v 
	coqc Quicksort.v
Repeat.vo: Repeat.v Lex.vo Prefix.vo Shorthand.vo 
	coqc Repeat.v
Shorthand.vo: Shorthand.v 
	coqc Shorthand.v
StrongDec.vo: StrongDec.v Shorthand.vo Prefix.vo Combi.vo 
	coqc StrongDec.v
Transports.vo: Transports.v Shorthand.vo 
	coqc Transports.v
