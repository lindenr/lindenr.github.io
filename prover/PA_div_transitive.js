window.requiredModules_div_transitive = ["addition_commutes","S_functional","addition_associates","distributivity","multiplication_associates","multiplication_commutes","nonzero_is_successor","addition_injective"];

window.proof_div_transitive = [
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
   "!<",
   "((@1)<(@2))=>(F)"
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
  "AddRelation",
  [
   2,
   "|",
   "Ex(((@1)*(x))=(@2))"
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
   "(x)|(y)"
  ],
  15,
  "(x)|(y)"
 ],
 [
  "Assume",
  [
   "(y)|(z)"
  ],
  16,
  "(y)|(z)"
 ],
 [
  "SubRelation",
  [
   15,
   "|",
   3
  ],
  17,
  "Ex0(((x)*(x0))=(y))"
 ],
 [
  "SubRelation",
  [
   16,
   "|",
   3
  ],
  18,
  "Ex(((y)*(x))=(z))"
 ],
 [
  "SV",
  [
   17,
   "#a"
  ],
  19,
  "((x)*(#a))=(y)"
 ],
 [
  "SV",
  [
   18,
   "#b"
  ],
  20,
  "((y)*(#b))=(z)"
 ],
 [
  "SV",
  [
   4,
   "((x)*(#a))*(#b)"
  ],
  21,
  "(((x)*(#a))*(#b))=(((x)*(#a))*(#b))"
 ],
 [
  "SV",
  [
   5,
   "(x)*(#a)"
  ],
  22,
  "Ay((((x)*(#a))=(y))=>((P[(x)*(#a)])=>(P[y])))"
 ],
 [
  "SV",
  [
   22,
   "y"
  ],
  23,
  "(((x)*(#a))=(y))=>((P[(x)*(#a)])=>(P[y]))"
 ],
 [
  "DEL",
  [
   22
  ],
  22,
  "Ay((((x)*(#a))=(y))=>((P[(x)*(#a)])=>(P[y])))"
 ],
 [
  "S",
  [
   23,
   "P",
   "(((x)*(#a))*(#b))=((@)*(#b))"
  ],
  24,
  "(((x)*(#a))=(y))=>(((((x)*(#a))*(#b))=(((x)*(#a))*(#b)))=>((((x)*(#a))*(#b))=((y)*(#b))))"
 ],
 [
  "DEL",
  [
   23
  ],
  23,
  "(((x)*(#a))=(y))=>((P[(x)*(#a)])=>(P[y]))"
 ],
 [
  "MP",
  [
   24,
   19
  ],
  25,
  "((((x)*(#a))*(#b))=(((x)*(#a))*(#b)))=>((((x)*(#a))*(#b))=((y)*(#b)))"
 ],
 [
  "MP",
  [
   25,
   21
  ],
  26,
  "(((x)*(#a))*(#b))=((y)*(#b))"
 ],
 [
  "DEL",
  [
   21
  ],
  21,
  "(((x)*(#a))*(#b))=(((x)*(#a))*(#b))"
 ],
 [
  "DEL",
  [
   24
  ],
  24,
  "(((x)*(#a))=(y))=>(((((x)*(#a))*(#b))=(((x)*(#a))*(#b)))=>((((x)*(#a))*(#b))=((y)*(#b))))"
 ],
 [
  "DEL",
  [
   25
  ],
  25,
  "((((x)*(#a))*(#b))=(((x)*(#a))*(#b)))=>((((x)*(#a))*(#b))=((y)*(#b)))"
 ],
 [
  "Highlight",
  [
   20
  ],
  20,
  "((y)*(#b))=(z)"
 ],
 [
  "Highlight",
  [
   26
  ],
  26,
  "(((x)*(#a))*(#b))=((y)*(#b))"
 ],
 [
  "SV",
  [
   5,
   "(y)*(#b)"
  ],
  27,
  "Ay0((((y)*(#b))=(y0))=>((P[(y)*(#b)])=>(P[y0])))"
 ],
 [
  "SV",
  [
   27,
   "z"
  ],
  28,
  "(((y)*(#b))=(z))=>((P[(y)*(#b)])=>(P[z]))"
 ],
 [
  "DEL",
  [
   27
  ],
  27,
  "Ay0((((y)*(#b))=(y0))=>((P[(y)*(#b)])=>(P[y0])))"
 ],
 [
  "S",
  [
   28,
   "P",
   "(((x)*(#a))*(#b))=(@)"
  ],
  29,
  "(((y)*(#b))=(z))=>(((((x)*(#a))*(#b))=((y)*(#b)))=>((((x)*(#a))*(#b))=(z)))"
 ],
 [
  "DEL",
  [
   28
  ],
  28,
  "(((y)*(#b))=(z))=>((P[(y)*(#b)])=>(P[z]))"
 ],
 [
  "MP",
  [
   29,
   20
  ],
  30,
  "((((x)*(#a))*(#b))=((y)*(#b)))=>((((x)*(#a))*(#b))=(z))"
 ],
 [
  "MP",
  [
   30,
   26
  ],
  31,
  "(((x)*(#a))*(#b))=(z)"
 ],
 [
  "DEL",
  [
   30
  ],
  30,
  "((((x)*(#a))*(#b))=((y)*(#b)))=>((((x)*(#a))*(#b))=(z))"
 ],
 [
  "DEL",
  [
   29
  ],
  29,
  "(((y)*(#b))=(z))=>(((((x)*(#a))*(#b))=((y)*(#b)))=>((((x)*(#a))*(#b))=(z)))"
 ],
 [
  "Highlight",
  [
   26
  ],
  26,
  "(((x)*(#a))*(#b))=((y)*(#b))"
 ],
 [
  "Highlight",
  [
   20
  ],
  20,
  "((y)*(#b))=(z)"
 ],
 [
  "Highlight",
  [
   31
  ],
  31,
  "(((x)*(#a))*(#b))=(z)"
 ],
 [
  "Quote",
  [
   "multiplication_associates"
  ],
  32,
  "Ax(Ay(Az((((x)*(y))*(z))=((x)*((y)*(z))))))"
 ],
 [
  "SV",
  [
   32,
   "x"
  ],
  33,
  "Ay(Az((((x)*(y))*(z))=((x)*((y)*(z)))))"
 ],
 [
  "SV",
  [
   33,
   "#a"
  ],
  34,
  "Az((((x)*(#a))*(z))=((x)*((#a)*(z))))"
 ],
 [
  "SV",
  [
   34,
   "#b"
  ],
  35,
  "(((x)*(#a))*(#b))=((x)*((#a)*(#b)))"
 ],
 [
  "Highlight",
  [
   35
  ],
  35,
  "(((x)*(#a))*(#b))=((x)*((#a)*(#b)))"
 ],
 [
  "SV",
  [
   5,
   "((x)*(#a))*(#b)"
  ],
  36,
  "Ay(((((x)*(#a))*(#b))=(y))=>((P[((x)*(#a))*(#b)])=>(P[y])))"
 ],
 [
  "SV",
  [
   36,
   "(x)*((#a)*(#b))"
  ],
  37,
  "((((x)*(#a))*(#b))=((x)*((#a)*(#b))))=>((P[((x)*(#a))*(#b)])=>(P[(x)*((#a)*(#b))]))"
 ],
 [
  "DEL",
  [
   36
  ],
  36,
  "Ay(((((x)*(#a))*(#b))=(y))=>((P[((x)*(#a))*(#b)])=>(P[y])))"
 ],
 [
  "S",
  [
   37,
   "P",
   "(@)=(z)"
  ],
  38,
  "((((x)*(#a))*(#b))=((x)*((#a)*(#b))))=>(((((x)*(#a))*(#b))=(z))=>(((x)*((#a)*(#b)))=(z)))"
 ],
 [
  "DEL",
  [
   37
  ],
  37,
  "((((x)*(#a))*(#b))=((x)*((#a)*(#b))))=>((P[((x)*(#a))*(#b)])=>(P[(x)*((#a)*(#b))]))"
 ],
 [
  "MP",
  [
   38,
   35
  ],
  39,
  "((((x)*(#a))*(#b))=(z))=>(((x)*((#a)*(#b)))=(z))"
 ],
 [
  "MP",
  [
   39,
   31
  ],
  40,
  "((x)*((#a)*(#b)))=(z)"
 ],
 [
  "DEL",
  [
   38
  ],
  38,
  "((((x)*(#a))*(#b))=((x)*((#a)*(#b))))=>(((((x)*(#a))*(#b))=(z))=>(((x)*((#a)*(#b)))=(z)))"
 ],
 [
  "DEL",
  [
   39
  ],
  39,
  "((((x)*(#a))*(#b))=(z))=>(((x)*((#a)*(#b)))=(z))"
 ],
 [
  "Highlight",
  [
   35
  ],
  35,
  "(((x)*(#a))*(#b))=((x)*((#a)*(#b)))"
 ],
 [
  "Highlight",
  [
   31
  ],
  31,
  "(((x)*(#a))*(#b))=(z)"
 ],
 [
  "GE",
  [
   40,
   "Ec(((x)*(c))=(z))"
  ],
  41,
  "Ec(((x)*(c))=(z))"
 ],
 [
  "Rewrite",
  [
   41,
   "(x)|(z)"
  ],
  42,
  "(x)|(z)"
 ],
 [
  "DT",
  [
   16,
   42
  ],
  43,
  "((y)|(z))=>((x)|(z))"
 ],
 [
  "DT",
  [
   15,
   43
  ],
  44,
  "((x)|(y))=>(((y)|(z))=>((x)|(z)))"
 ],
 [
  "G",
  [
   44,
   "z"
  ],
  45,
  "Az(((x)|(y))=>(((y)|(z))=>((x)|(z))))"
 ],
 [
  "G",
  [
   45,
   "y"
  ],
  46,
  "Ay(Az(((x)|(y))=>(((y)|(z))=>((x)|(z)))))"
 ],
 [
  "G",
  [
   46,
   "x"
  ],
  47,
  "Ax(Ay(Az(((x)|(y))=>(((y)|(z))=>((x)|(z))))))"
 ],
 [
  "Highlight",
  [
   47
  ],
  47,
  "Ax(Ay(Az(((x)|(y))=>(((y)|(z))=>((x)|(z))))))"
 ]
];