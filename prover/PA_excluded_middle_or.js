window.requiredModules_excluded_middle_or = [];
window.proof_excluded_middle_or = [
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
   "(P)=>(F)"
  ],
  15,
  "(P)=>(F)"
 ],
 [
  "Assume",
  [
   "P"
  ],
  16,
  "P"
 ],
 [
  "MP",
  [
   15,
   16
  ],
  17,
  "F"
 ],
 [
  "DT",
  [
   16,
   17
  ],
  18,
  "(P)=>(F)"
 ],
 [
  "DT",
  [
   15,
   18
  ],
  19,
  "((P)=>(F))=>((P)=>(F))"
 ],
 [
  "Rewrite",
  [
   19,
   "(P)||((P)=>(F))"
  ],
  20,
  "(P)||((P)=>(F))"
 ],
 [
  "DEL",
  [
   15
  ],
  15,
  "(P)=>(F)"
 ],
 [
  "DEL",
  [
   16
  ],
  16,
  "P"
 ],
 [
  "DEL",
  [
   17
  ],
  17,
  "F"
 ],
 [
  "DEL",
  [
   18
  ],
  18,
  "(P)=>(F)"
 ],
 [
  "DEL",
  [
   19
  ],
  19,
  "((P)=>(F))=>((P)=>(F))"
 ]
];