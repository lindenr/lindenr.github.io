window.requiredModules_alternative_implication = [];
window.proof_alternative_implication = [
 [
  "AddRelation",
  [
   2,
   "<=",
   "Ex(((@1)+(x))=(@2))"
  ],
  null,
  ""
 ],
 [
  "AddRelation",
  [
   2,
   "<",
   "Ex(((@1)+(S(x)))=(@2))"
  ],
  null,
  ""
 ],
 [
  "AddRelation",
  [
   2,
   "!=",
   "((@1)=(@2))=>(F)"
  ],
  null,
  ""
 ],
 [
  "AddConnective",
  [
   2,
   "||",
   "((P)=>(F))=>(Q)"
  ],
  null,
  ""
 ],
 [
  "AddConnective",
  [
   2,
   "&&",
   "((P)=>((Q)=>(F)))=>(F)"
  ],
  null,
  ""
 ],
 [
  "Assume",
  [
   "(P)=>(Q)"
  ],
  15,
  "(P)=>(Q)"
 ],
 [
  "Assume",
  [
   "((P)=>(F))=>(Q)"
  ],
  16,
  "((P)=>(F))=>(Q)"
 ],
 [
  "Assume",
  [
   "(Q)=>(F)"
  ],
  17,
  "(Q)=>(F)"
 ],
 [
  "Assume",
  [
   "P"
  ],
  18,
  "P"
 ],
 [
  "MP",
  [
   15,
   18
  ],
  19,
  "Q"
 ],
 [
  "MP",
  [
   17,
   19
  ],
  20,
  "F"
 ],
 [
  "DT",
  [
   18,
   20
  ],
  21,
  "(P)=>(F)"
 ],
 [
  "Assume",
  [
   "(P)=>(F)"
  ],
  22,
  "(P)=>(F)"
 ],
 [
  "MP",
  [
   16,
   22
  ],
  23,
  "Q"
 ],
 [
  "MP",
  [
   17,
   23
  ],
  24,
  "F"
 ],
 [
  "DT",
  [
   22,
   24
  ],
  25,
  "((P)=>(F))=>(F)"
 ],
 [
  "MP",
  [
   25,
   21
  ],
  26,
  "F"
 ],
 [
  "DT",
  [
   17,
   26
  ],
  27,
  "((Q)=>(F))=>(F)"
 ],
 [
  "S",
  [
   3,
   "P",
   "Q"
  ],
  28,
  "(((Q)=>(F))=>(F))=>(Q)"
 ],
 [
  "MP",
  [
   28,
   27
  ],
  29,
  "Q"
 ],
 [
  "DT",
  [
   16,
   29
  ],
  30,
  "(((P)=>(F))=>(Q))=>(Q)"
 ],
 [
  "DT",
  [
   15,
   30
  ],
  31,
  "((P)=>(Q))=>((((P)=>(F))=>(Q))=>(Q))"
 ]
];