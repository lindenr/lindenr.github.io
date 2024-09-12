window.requiredModules_lt_asymmetric = ["addition_commutes","addition_injective","S_functional","addition_associates","nonzero_is_successor","explosion","equal_or_unequal","or_implies","add_to_0","addition"];

window.proof_lt_asymmetric = [
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
   "(x)<(y)"
  ],
  15,
  "(x)<(y)"
 ],
 [
  "Assume",
  [
   "(y)<(x)"
  ],
  16,
  "(y)<(x)"
 ],
 [
  "SubRelation",
  [
   15,
   "<",
   3
  ],
  17,
  "Ex0(((x)+(S(x0)))=(y))"
 ],
 [
  "SubRelation",
  [
   16,
   "<",
   3
  ],
  18,
  "Ex0(((y)+(S(x0)))=(x))"
 ],
 [
  "SV",
  [
   17,
   "#a"
  ],
  19,
  "((x)+(S(#a)))=(y)"
 ],
 [
  "SV",
  [
   18,
   "#b"
  ],
  20,
  "((y)+(S(#b)))=(x)"
 ],
 [
  "SV",
  [
   4,
   "((x)+(S(#a)))+(S(#b))"
  ],
  21,
  "(((x)+(S(#a)))+(S(#b)))=(((x)+(S(#a)))+(S(#b)))"
 ],
 [
  "SV",
  [
   5,
   "(x)+(S(#a))"
  ],
  22,
  "Ay((((x)+(S(#a)))=(y))=>((P[(x)+(S(#a))])=>(P[y])))"
 ],
 [
  "SV",
  [
   22,
   "y"
  ],
  23,
  "(((x)+(S(#a)))=(y))=>((P[(x)+(S(#a))])=>(P[y]))"
 ],
 [
  "DEL",
  [
   22
  ],
  22,
  "Ay((((x)+(S(#a)))=(y))=>((P[(x)+(S(#a))])=>(P[y])))"
 ],
 [
  "S",
  [
   23,
   "P",
   "(((x)+(S(#a)))+(S(#b)))=((@)+(S(#b)))"
  ],
  24,
  "(((x)+(S(#a)))=(y))=>(((((x)+(S(#a)))+(S(#b)))=(((x)+(S(#a)))+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b)))))"
 ],
 [
  "DEL",
  [
   23
  ],
  23,
  "(((x)+(S(#a)))=(y))=>((P[(x)+(S(#a))])=>(P[y]))"
 ],
 [
  "MP",
  [
   24,
   19
  ],
  25,
  "((((x)+(S(#a)))+(S(#b)))=(((x)+(S(#a)))+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b))))"
 ],
 [
  "MP",
  [
   25,
   21
  ],
  26,
  "(((x)+(S(#a)))+(S(#b)))=((y)+(S(#b)))"
 ],
 [
  "DEL",
  [
   21
  ],
  21,
  "(((x)+(S(#a)))+(S(#b)))=(((x)+(S(#a)))+(S(#b)))"
 ],
 [
  "DEL",
  [
   24
  ],
  24,
  "(((x)+(S(#a)))=(y))=>(((((x)+(S(#a)))+(S(#b)))=(((x)+(S(#a)))+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b)))))"
 ],
 [
  "DEL",
  [
   25
  ],
  25,
  "((((x)+(S(#a)))+(S(#b)))=(((x)+(S(#a)))+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b))))"
 ],
 [
  "Highlight",
  [
   20
  ],
  20,
  "((y)+(S(#b)))=(x)"
 ],
 [
  "Highlight",
  [
   26
  ],
  26,
  "(((x)+(S(#a)))+(S(#b)))=((y)+(S(#b)))"
 ],
 [
  "SV",
  [
   5,
   "(y)+(S(#b))"
  ],
  27,
  "Ay0((((y)+(S(#b)))=(y0))=>((P[(y)+(S(#b))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   27,
   "x"
  ],
  28,
  "(((y)+(S(#b)))=(x))=>((P[(y)+(S(#b))])=>(P[x]))"
 ],
 [
  "DEL",
  [
   27
  ],
  27,
  "Ay0((((y)+(S(#b)))=(y0))=>((P[(y)+(S(#b))])=>(P[y0])))"
 ],
 [
  "S",
  [
   28,
   "P",
   "(((x)+(S(#a)))+(S(#b)))=(@)"
  ],
  29,
  "(((y)+(S(#b)))=(x))=>(((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=(x)))"
 ],
 [
  "DEL",
  [
   28
  ],
  28,
  "(((y)+(S(#b)))=(x))=>((P[(y)+(S(#b))])=>(P[x]))"
 ],
 [
  "MP",
  [
   29,
   20
  ],
  30,
  "((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=(x))"
 ],
 [
  "MP",
  [
   30,
   26
  ],
  31,
  "(((x)+(S(#a)))+(S(#b)))=(x)"
 ],
 [
  "DEL",
  [
   30
  ],
  30,
  "((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=(x))"
 ],
 [
  "DEL",
  [
   29
  ],
  29,
  "(((y)+(S(#b)))=(x))=>(((((x)+(S(#a)))+(S(#b)))=((y)+(S(#b))))=>((((x)+(S(#a)))+(S(#b)))=(x)))"
 ],
 [
  "Quote",
  [
   "addition_injective"
  ],
  32,
  "Ax(Aa(Ab((((x)+(a))=((x)+(b)))=>((a)=(b)))))"
 ],
 [
  "Quote",
  [
   "addition_associates"
  ],
  33,
  "Ax(Ay(Az((((x)+(y))+(z))=((x)+((y)+(z))))))"
 ],
 [
  "SV",
  [
   33,
   "x"
  ],
  34,
  "Ay(Az((((x)+(y))+(z))=((x)+((y)+(z)))))"
 ],
 [
  "SV",
  [
   34,
   "S(#a)"
  ],
  35,
  "Az((((x)+(S(#a)))+(z))=((x)+((S(#a))+(z))))"
 ],
 [
  "SV",
  [
   35,
   "S(#b)"
  ],
  36,
  "(((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "Highlight",
  [
   26
  ],
  26,
  "(((x)+(S(#a)))+(S(#b)))=((y)+(S(#b)))"
 ],
 [
  "Highlight",
  [
   20
  ],
  20,
  "((y)+(S(#b)))=(x)"
 ],
 [
  "Highlight",
  [
   33
  ],
  33,
  "Ax(Ay(Az((((x)+(y))+(z))=((x)+((y)+(z))))))"
 ],
 [
  "Highlight",
  [
   36
  ],
  36,
  "(((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "Highlight",
  [
   33
  ],
  33,
  "Ax(Ay(Az((((x)+(y))+(z))=((x)+((y)+(z))))))"
 ],
 [
  "Highlight",
  [
   31
  ],
  31,
  "(((x)+(S(#a)))+(S(#b)))=(x)"
 ],
 [
  "SV",
  [
   5,
   "((x)+(S(#a)))+(S(#b))"
  ],
  37,
  "Ay(((((x)+(S(#a)))+(S(#b)))=(y))=>((P[((x)+(S(#a)))+(S(#b))])=>(P[y])))"
 ],
 [
  "SV",
  [
   37,
   "(x)+((S(#a))+(S(#b)))"
  ],
  38,
  "((((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b)))))=>((P[((x)+(S(#a)))+(S(#b))])=>(P[(x)+((S(#a))+(S(#b)))]))"
 ],
 [
  "DEL",
  [
   37
  ],
  37,
  "Ay(((((x)+(S(#a)))+(S(#b)))=(y))=>((P[((x)+(S(#a)))+(S(#b))])=>(P[y])))"
 ],
 [
  "S",
  [
   38,
   "P",
   "(@)=(x)"
  ],
  39,
  "((((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b)))))=>(((((x)+(S(#a)))+(S(#b)))=(x))=>(((x)+((S(#a))+(S(#b))))=(x)))"
 ],
 [
  "DEL",
  [
   38
  ],
  38,
  "((((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b)))))=>((P[((x)+(S(#a)))+(S(#b))])=>(P[(x)+((S(#a))+(S(#b)))]))"
 ],
 [
  "MP",
  [
   39,
   36
  ],
  40,
  "((((x)+(S(#a)))+(S(#b)))=(x))=>(((x)+((S(#a))+(S(#b))))=(x))"
 ],
 [
  "MP",
  [
   40,
   31
  ],
  41,
  "((x)+((S(#a))+(S(#b))))=(x)"
 ],
 [
  "DEL",
  [
   39
  ],
  39,
  "((((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b)))))=>(((((x)+(S(#a)))+(S(#b)))=(x))=>(((x)+((S(#a))+(S(#b))))=(x)))"
 ],
 [
  "DEL",
  [
   40
  ],
  40,
  "((((x)+(S(#a)))+(S(#b)))=(x))=>(((x)+((S(#a))+(S(#b))))=(x))"
 ],
 [
  "Highlight",
  [
   36
  ],
  36,
  "(((x)+(S(#a)))+(S(#b)))=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "Highlight",
  [
   31
  ],
  31,
  "(((x)+(S(#a)))+(S(#b)))=(x)"
 ],
 [
  "Highlight",
  [
   41
  ],
  41,
  "((x)+((S(#a))+(S(#b))))=(x)"
 ],
 [
  "SV",
  [
   10,
   "x"
  ],
  42,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   42
  ],
  42,
  "((x)+(0))=(x)"
 ],
 [
  "SV",
  [
   5,
   "(x)+((S(#a))+(S(#b)))"
  ],
  43,
  "Ay((((x)+((S(#a))+(S(#b))))=(y))=>((P[(x)+((S(#a))+(S(#b)))])=>(P[y])))"
 ],
 [
  "SV",
  [
   43,
   "x"
  ],
  44,
  "(((x)+((S(#a))+(S(#b))))=(x))=>((P[(x)+((S(#a))+(S(#b)))])=>(P[x]))"
 ],
 [
  "DEL",
  [
   43
  ],
  43,
  "Ay((((x)+((S(#a))+(S(#b))))=(y))=>((P[(x)+((S(#a))+(S(#b)))])=>(P[y])))"
 ],
 [
  "S",
  [
   44,
   "P",
   "(@)=((x)+((S(#a))+(S(#b))))"
  ],
  45,
  "(((x)+((S(#a))+(S(#b))))=(x))=>((((x)+((S(#a))+(S(#b))))=((x)+((S(#a))+(S(#b)))))=>((x)=((x)+((S(#a))+(S(#b))))))"
 ],
 [
  "DEL",
  [
   44
  ],
  44,
  "(((x)+((S(#a))+(S(#b))))=(x))=>((P[(x)+((S(#a))+(S(#b)))])=>(P[x]))"
 ],
 [
  "SV",
  [
   4,
   "(x)+((S(#a))+(S(#b)))"
  ],
  46,
  "((x)+((S(#a))+(S(#b))))=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "MP",
  [
   45,
   41
  ],
  47,
  "(((x)+((S(#a))+(S(#b))))=((x)+((S(#a))+(S(#b)))))=>((x)=((x)+((S(#a))+(S(#b)))))"
 ],
 [
  "MP",
  [
   47,
   46
  ],
  48,
  "(x)=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "SV",
  [
   5,
   "x"
  ],
  49,
  "Ay(((x)=(y))=>((P[x])=>(P[y])))"
 ],
 [
  "SV",
  [
   49,
   "(x)+((S(#a))+(S(#b)))"
  ],
  50,
  "((x)=((x)+((S(#a))+(S(#b)))))=>((P[x])=>(P[(x)+((S(#a))+(S(#b)))]))"
 ],
 [
  "DEL",
  [
   49
  ],
  49,
  "Ay(((x)=(y))=>((P[x])=>(P[y])))"
 ],
 [
  "S",
  [
   50,
   "P",
   "((x)+(0))=(@)"
  ],
  51,
  "((x)=((x)+((S(#a))+(S(#b)))))=>((((x)+(0))=(x))=>(((x)+(0))=((x)+((S(#a))+(S(#b))))))"
 ],
 [
  "DEL",
  [
   50
  ],
  50,
  "((x)=((x)+((S(#a))+(S(#b)))))=>((P[x])=>(P[(x)+((S(#a))+(S(#b)))]))"
 ],
 [
  "MP",
  [
   51,
   48
  ],
  52,
  "(((x)+(0))=(x))=>(((x)+(0))=((x)+((S(#a))+(S(#b)))))"
 ],
 [
  "MP",
  [
   52,
   42
  ],
  53,
  "((x)+(0))=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "DEL",
  [
   45
  ],
  45,
  "(((x)+((S(#a))+(S(#b))))=(x))=>((((x)+((S(#a))+(S(#b))))=((x)+((S(#a))+(S(#b)))))=>((x)=((x)+((S(#a))+(S(#b))))))"
 ],
 [
  "DEL",
  [
   46
  ],
  46,
  "((x)+((S(#a))+(S(#b))))=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "DEL",
  [
   47
  ],
  47,
  "(((x)+((S(#a))+(S(#b))))=((x)+((S(#a))+(S(#b)))))=>((x)=((x)+((S(#a))+(S(#b)))))"
 ],
 [
  "DEL",
  [
   48
  ],
  48,
  "(x)=((x)+((S(#a))+(S(#b))))"
 ],
 [
  "DEL",
  [
   51
  ],
  51,
  "((x)=((x)+((S(#a))+(S(#b)))))=>((((x)+(0))=(x))=>(((x)+(0))=((x)+((S(#a))+(S(#b))))))"
 ],
 [
  "DEL",
  [
   52
  ],
  52,
  "(((x)+(0))=(x))=>(((x)+(0))=((x)+((S(#a))+(S(#b)))))"
 ],
 [
  "Highlight",
  [
   42
  ],
  42,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   41
  ],
  41,
  "((x)+((S(#a))+(S(#b))))=(x)"
 ],
 [
  "SV",
  [
   32,
   "x"
  ],
  54,
  "Aa(Ab((((x)+(a))=((x)+(b)))=>((a)=(b))))"
 ],
 [
  "SV",
  [
   54,
   "0"
  ],
  55,
  "Ab((((x)+(0))=((x)+(b)))=>((0)=(b)))"
 ],
 [
  "SV",
  [
   55,
   "(S(#a))+(S(#b))"
  ],
  56,
  "(((x)+(0))=((x)+((S(#a))+(S(#b)))))=>((0)=((S(#a))+(S(#b))))"
 ],
 [
  "MP",
  [
   56,
   53
  ],
  57,
  "(0)=((S(#a))+(S(#b)))"
 ],
 [
  "SV",
  [
   11,
   "S(#a)"
  ],
  58,
  "Ay(((S(#a))+(S(y)))=(S((S(#a))+(y))))"
 ],
 [
  "SV",
  [
   58,
   "#b"
  ],
  59,
  "((S(#a))+(S(#b)))=(S((S(#a))+(#b)))"
 ],
 [
  "Highlight",
  [
   57
  ],
  57,
  "(0)=((S(#a))+(S(#b)))"
 ],
 [
  "Highlight",
  [
   59
  ],
  59,
  "((S(#a))+(S(#b)))=(S((S(#a))+(#b)))"
 ],
 [
  "SV",
  [
   5,
   "(S(#a))+(S(#b))"
  ],
  60,
  "Ay((((S(#a))+(S(#b)))=(y))=>((P[(S(#a))+(S(#b))])=>(P[y])))"
 ],
 [
  "SV",
  [
   60,
   "S((S(#a))+(#b))"
  ],
  61,
  "(((S(#a))+(S(#b)))=(S((S(#a))+(#b))))=>((P[(S(#a))+(S(#b))])=>(P[S((S(#a))+(#b))]))"
 ],
 [
  "DEL",
  [
   60
  ],
  60,
  "Ay((((S(#a))+(S(#b)))=(y))=>((P[(S(#a))+(S(#b))])=>(P[y])))"
 ],
 [
  "S",
  [
   61,
   "P",
   "(0)=(@)"
  ],
  62,
  "(((S(#a))+(S(#b)))=(S((S(#a))+(#b))))=>(((0)=((S(#a))+(S(#b))))=>((0)=(S((S(#a))+(#b)))))"
 ],
 [
  "DEL",
  [
   61
  ],
  61,
  "(((S(#a))+(S(#b)))=(S((S(#a))+(#b))))=>((P[(S(#a))+(S(#b))])=>(P[S((S(#a))+(#b))]))"
 ],
 [
  "MP",
  [
   62,
   59
  ],
  63,
  "((0)=((S(#a))+(S(#b))))=>((0)=(S((S(#a))+(#b))))"
 ],
 [
  "MP",
  [
   63,
   57
  ],
  64,
  "(0)=(S((S(#a))+(#b)))"
 ],
 [
  "DEL",
  [
   63
  ],
  63,
  "((0)=((S(#a))+(S(#b))))=>((0)=(S((S(#a))+(#b))))"
 ],
 [
  "DEL",
  [
   62
  ],
  62,
  "(((S(#a))+(S(#b)))=(S((S(#a))+(#b))))=>(((0)=((S(#a))+(S(#b))))=>((0)=(S((S(#a))+(#b)))))"
 ],
 [
  "Highlight",
  [
   59
  ],
  59,
  "((S(#a))+(S(#b)))=(S((S(#a))+(#b)))"
 ],
 [
  "Highlight",
  [
   57
  ],
  57,
  "(0)=((S(#a))+(S(#b)))"
 ],
 [
  "Highlight",
  [
   64
  ],
  64,
  "(0)=(S((S(#a))+(#b)))"
 ],
 [
  "SV",
  [
   5,
   "0"
  ],
  65,
  "Ay(((0)=(y))=>((P[0])=>(P[y])))"
 ],
 [
  "SV",
  [
   65,
   "S((S(#a))+(#b))"
  ],
  66,
  "((0)=(S((S(#a))+(#b))))=>((P[0])=>(P[S((S(#a))+(#b))]))"
 ],
 [
  "DEL",
  [
   65
  ],
  65,
  "Ay(((0)=(y))=>((P[0])=>(P[y])))"
 ],
 [
  "S",
  [
   66,
   "P",
   "(@)=(0)"
  ],
  67,
  "((0)=(S((S(#a))+(#b))))=>(((0)=(0))=>((S((S(#a))+(#b)))=(0)))"
 ],
 [
  "DEL",
  [
   66
  ],
  66,
  "((0)=(S((S(#a))+(#b))))=>((P[0])=>(P[S((S(#a))+(#b))]))"
 ],
 [
  "SV",
  [
   4,
   "0"
  ],
  68,
  "(0)=(0)"
 ],
 [
  "MP",
  [
   67,
   64
  ],
  69,
  "((0)=(0))=>((S((S(#a))+(#b)))=(0))"
 ],
 [
  "MP",
  [
   69,
   68
  ],
  70,
  "(S((S(#a))+(#b)))=(0)"
 ],
 [
  "DEL",
  [
   67
  ],
  67,
  "((0)=(S((S(#a))+(#b))))=>(((0)=(0))=>((S((S(#a))+(#b)))=(0)))"
 ],
 [
  "DEL",
  [
   68
  ],
  68,
  "(0)=(0)"
 ],
 [
  "DEL",
  [
   69
  ],
  69,
  "((0)=(0))=>((S((S(#a))+(#b)))=(0))"
 ],
 [
  "Highlight",
  [
   70
  ],
  70,
  "(S((S(#a))+(#b)))=(0)"
 ],
 [
  "Highlight",
  [
   64
  ],
  64,
  "(0)=(S((S(#a))+(#b)))"
 ],
 [
  "SV",
  [
   9,
   "(S(#a))+(#b)"
  ],
  71,
  "((S((S(#a))+(#b)))=(0))=>(F)"
 ],
 [
  "MP",
  [
   71,
   70
  ],
  72,
  "F"
 ],
 [
  "DT",
  [
   16,
   72
  ],
  73,
  "((y)<(x))=>(F)"
 ],
 [
  "Rewrite",
  [
   73,
   "(y)!<(x)"
  ],
  74,
  "(y)!<(x)"
 ],
 [
  "DT",
  [
   15,
   74
  ],
  75,
  "((x)<(y))=>((y)!<(x))"
 ],
 [
  "G",
  [
   75,
   "y"
  ],
  76,
  "Ay(((x)<(y))=>((y)!<(x)))"
 ],
 [
  "G",
  [
   76,
   "x"
  ],
  77,
  "Ax(Ay(((x)<(y))=>((y)!<(x))))"
 ]
];