window.requiredModules_lt_irreflexive = ["addition_commutes","addition_injective","S_functional","addition_associates","nonzero_is_successor","explosion","equal_or_unequal","or_implies","add_to_0","addition"];

window.proof_lt_irreflexive = [
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
   "(x)<(x)"
  ],
  15,
  "(x)<(x)"
 ],
 [
  "SubRelation",
  [
   15,
   "<",
   3
  ],
  16,
  "Ex0(((x)+(S(x0)))=(x))"
 ],
 [
  "SV",
  [
   16,
   "#a"
  ],
  17,
  "((x)+(S(#a)))=(x)"
 ],
 [
  "SV",
  [
   10,
   "x"
  ],
  18,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   17
  ],
  17,
  "((x)+(S(#a)))=(x)"
 ],
 [
  "Highlight",
  [
   18
  ],
  18,
  "((x)+(0))=(x)"
 ],
 [
  "SV",
  [
   5,
   "(x)+(S(#a))"
  ],
  19,
  "Ay((((x)+(S(#a)))=(y))=>((P[(x)+(S(#a))])=>(P[y])))"
 ],
 [
  "SV",
  [
   19,
   "x"
  ],
  20,
  "(((x)+(S(#a)))=(x))=>((P[(x)+(S(#a))])=>(P[x]))"
 ],
 [
  "DEL",
  [
   19
  ],
  19,
  "Ay((((x)+(S(#a)))=(y))=>((P[(x)+(S(#a))])=>(P[y])))"
 ],
 [
  "S",
  [
   20,
   "P",
   "(@)=((x)+(S(#a)))"
  ],
  21,
  "(((x)+(S(#a)))=(x))=>((((x)+(S(#a)))=((x)+(S(#a))))=>((x)=((x)+(S(#a)))))"
 ],
 [
  "DEL",
  [
   20
  ],
  20,
  "(((x)+(S(#a)))=(x))=>((P[(x)+(S(#a))])=>(P[x]))"
 ],
 [
  "SV",
  [
   4,
   "(x)+(S(#a))"
  ],
  22,
  "((x)+(S(#a)))=((x)+(S(#a)))"
 ],
 [
  "MP",
  [
   21,
   17
  ],
  23,
  "(((x)+(S(#a)))=((x)+(S(#a))))=>((x)=((x)+(S(#a))))"
 ],
 [
  "MP",
  [
   23,
   22
  ],
  24,
  "(x)=((x)+(S(#a)))"
 ],
 [
  "SV",
  [
   5,
   "x"
  ],
  25,
  "Ay(((x)=(y))=>((P[x])=>(P[y])))"
 ],
 [
  "SV",
  [
   25,
   "(x)+(S(#a))"
  ],
  26,
  "((x)=((x)+(S(#a))))=>((P[x])=>(P[(x)+(S(#a))]))"
 ],
 [
  "DEL",
  [
   25
  ],
  25,
  "Ay(((x)=(y))=>((P[x])=>(P[y])))"
 ],
 [
  "S",
  [
   26,
   "P",
   "((x)+(0))=(@)"
  ],
  27,
  "((x)=((x)+(S(#a))))=>((((x)+(0))=(x))=>(((x)+(0))=((x)+(S(#a)))))"
 ],
 [
  "DEL",
  [
   26
  ],
  26,
  "((x)=((x)+(S(#a))))=>((P[x])=>(P[(x)+(S(#a))]))"
 ],
 [
  "MP",
  [
   27,
   24
  ],
  28,
  "(((x)+(0))=(x))=>(((x)+(0))=((x)+(S(#a))))"
 ],
 [
  "MP",
  [
   28,
   18
  ],
  29,
  "((x)+(0))=((x)+(S(#a)))"
 ],
 [
  "DEL",
  [
   21
  ],
  21,
  "(((x)+(S(#a)))=(x))=>((((x)+(S(#a)))=((x)+(S(#a))))=>((x)=((x)+(S(#a)))))"
 ],
 [
  "DEL",
  [
   22
  ],
  22,
  "((x)+(S(#a)))=((x)+(S(#a)))"
 ],
 [
  "DEL",
  [
   23
  ],
  23,
  "(((x)+(S(#a)))=((x)+(S(#a))))=>((x)=((x)+(S(#a))))"
 ],
 [
  "DEL",
  [
   24
  ],
  24,
  "(x)=((x)+(S(#a)))"
 ],
 [
  "DEL",
  [
   27
  ],
  27,
  "((x)=((x)+(S(#a))))=>((((x)+(0))=(x))=>(((x)+(0))=((x)+(S(#a)))))"
 ],
 [
  "DEL",
  [
   28
  ],
  28,
  "(((x)+(0))=(x))=>(((x)+(0))=((x)+(S(#a))))"
 ],
 [
  "Highlight",
  [
   18
  ],
  18,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   17
  ],
  17,
  "((x)+(S(#a)))=(x)"
 ],
 [
  "Quote",
  [
   "addition_injective"
  ],
  30,
  "Ax(Aa(Ab((((x)+(a))=((x)+(b)))=>((a)=(b)))))"
 ],
 [
  "SV",
  [
   30,
   "x"
  ],
  31,
  "Aa(Ab((((x)+(a))=((x)+(b)))=>((a)=(b))))"
 ],
 [
  "SV",
  [
   31,
   "0"
  ],
  32,
  "Ab((((x)+(0))=((x)+(b)))=>((0)=(b)))"
 ],
 [
  "SV",
  [
   32,
   "S(#a)"
  ],
  33,
  "(((x)+(0))=((x)+(S(#a))))=>((0)=(S(#a)))"
 ],
 [
  "MP",
  [
   33,
   29
  ],
  34,
  "(0)=(S(#a))"
 ],
 [
  "Highlight",
  [
   34
  ],
  34,
  "(0)=(S(#a))"
 ],
 [
  "SV",
  [
   5,
   "0"
  ],
  35,
  "Ay(((0)=(y))=>((P[0])=>(P[y])))"
 ],
 [
  "SV",
  [
   35,
   "S(#a)"
  ],
  36,
  "((0)=(S(#a)))=>((P[0])=>(P[S(#a)]))"
 ],
 [
  "DEL",
  [
   35
  ],
  35,
  "Ay(((0)=(y))=>((P[0])=>(P[y])))"
 ],
 [
  "S",
  [
   36,
   "P",
   "(@)=(0)"
  ],
  37,
  "((0)=(S(#a)))=>(((0)=(0))=>((S(#a))=(0)))"
 ],
 [
  "DEL",
  [
   36
  ],
  36,
  "((0)=(S(#a)))=>((P[0])=>(P[S(#a)]))"
 ],
 [
  "SV",
  [
   4,
   "0"
  ],
  38,
  "(0)=(0)"
 ],
 [
  "MP",
  [
   37,
   34
  ],
  39,
  "((0)=(0))=>((S(#a))=(0))"
 ],
 [
  "MP",
  [
   39,
   38
  ],
  40,
  "(S(#a))=(0)"
 ],
 [
  "DEL",
  [
   37
  ],
  37,
  "((0)=(S(#a)))=>(((0)=(0))=>((S(#a))=(0)))"
 ],
 [
  "DEL",
  [
   38
  ],
  38,
  "(0)=(0)"
 ],
 [
  "DEL",
  [
   39
  ],
  39,
  "((0)=(0))=>((S(#a))=(0))"
 ],
 [
  "Highlight",
  [
   34
  ],
  34,
  "(0)=(S(#a))"
 ],
 [
  "SV",
  [
   9,
   "#a"
  ],
  41,
  "((S(#a))=(0))=>(F)"
 ],
 [
  "MP",
  [
   41,
   40
  ],
  42,
  "F"
 ],
 [
  "DT",
  [
   15,
   42
  ],
  43,
  "((x)<(x))=>(F)"
 ],
 [
  "Rewrite",
  [
   43,
   "(x)!<(x)"
  ],
  44,
  "(x)!<(x)"
 ],
 [
  "G",
  [
   44,
   "x"
  ],
  45,
  "Ax((x)!<(x))"
 ]
];