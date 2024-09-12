window.requiredModules_lt_trichotomous = ["addition_commutes","explosion","nonzero_is_successor","S_preserves_leq","or_implies","excluded_middle_or","leq_total","S_functional","addition_associates","leq_transitive","leq_reflexive","and_elimination1","and_elimination2","addition_injective","equal_or_unequal","add_to_0","leq_antisymmetric","leq","equal_or_unequal","nonzero_is_successor","alternative_implication","or_introduction1","logic","or_commutes"];

window.proof_lt_trichotomous = [
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
   "(x)!=(y)"
  ],
  15,
  "(x)!=(y)"
 ],
 [
  "SubRelation",
  [
   15,
   "!=",
   3
  ],
  16,
  "((x)=(y))=>(F)"
 ],
 [
  "Quote",
  [
   "leq_total"
  ],
  17,
  "Ax(Ay(((x)<=(y))||((y)<=(x))))"
 ],
 [
  "SV",
  [
   17,
   "x"
  ],
  18,
  "Ay(((x)<=(y))||((y)<=(x)))"
 ],
 [
  "SV",
  [
   18,
   "y"
  ],
  19,
  "((x)<=(y))||((y)<=(x))"
 ],
 [
  "Assume",
  [
   "(x)<=(y)"
  ],
  20,
  "(x)<=(y)"
 ],
 [
  "SubRelation",
  [
   20,
   "<=",
   3
  ],
  21,
  "Ex0(((x)+(x0))=(y))"
 ],
 [
  "SV",
  [
   21,
   "#a"
  ],
  22,
  "((x)+(#a))=(y)"
 ],
 [
  "Assume",
  [
   "(#a)=(0)"
  ],
  23,
  "(#a)=(0)"
 ],
 [
  "SV",
  [
   4,
   "(x)+(#a)"
  ],
  24,
  "((x)+(#a))=((x)+(#a))"
 ],
 [
  "SV",
  [
   5,
   "#a"
  ],
  25,
  "Ay(((#a)=(y))=>((P[#a])=>(P[y])))"
 ],
 [
  "SV",
  [
   25,
   "0"
  ],
  26,
  "((#a)=(0))=>((P[#a])=>(P[0]))"
 ],
 [
  "DEL",
  [
   25
  ],
  25,
  "Ay(((#a)=(y))=>((P[#a])=>(P[y])))"
 ],
 [
  "S",
  [
   26,
   "P",
   "((x)+(#a))=((x)+(@))"
  ],
  27,
  "((#a)=(0))=>((((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0))))"
 ],
 [
  "DEL",
  [
   26
  ],
  26,
  "((#a)=(0))=>((P[#a])=>(P[0]))"
 ],
 [
  "MP",
  [
   27,
   23
  ],
  28,
  "(((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0)))"
 ],
 [
  "MP",
  [
   28,
   24
  ],
  29,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "DEL",
  [
   24
  ],
  24,
  "((x)+(#a))=((x)+(#a))"
 ],
 [
  "DEL",
  [
   27
  ],
  27,
  "((#a)=(0))=>((((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0))))"
 ],
 [
  "DEL",
  [
   28
  ],
  28,
  "(((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0)))"
 ],
 [
  "Highlight",
  [
   22
  ],
  22,
  "((x)+(#a))=(y)"
 ],
 [
  "Highlight",
  [
   29
  ],
  29,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "Highlight",
  [
   29
  ],
  29,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "Highlight",
  [
   29
  ],
  29,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "SV",
  [
   5,
   "(x)+(#a)"
  ],
  30,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "SV",
  [
   30,
   "(x)+(0)"
  ],
  31,
  "(((x)+(#a))=((x)+(0)))=>((P[(x)+(#a)])=>(P[(x)+(0)]))"
 ],
 [
  "DEL",
  [
   30
  ],
  30,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "S",
  [
   31,
   "P",
   "(@)=(y)"
  ],
  32,
  "(((x)+(#a))=((x)+(0)))=>((((x)+(#a))=(y))=>(((x)+(0))=(y)))"
 ],
 [
  "DEL",
  [
   31
  ],
  31,
  "(((x)+(#a))=((x)+(0)))=>((P[(x)+(#a)])=>(P[(x)+(0)]))"
 ],
 [
  "MP",
  [
   32,
   29
  ],
  33,
  "(((x)+(#a))=(y))=>(((x)+(0))=(y))"
 ],
 [
  "MP",
  [
   33,
   22
  ],
  34,
  "((x)+(0))=(y)"
 ],
 [
  "DEL",
  [
   32
  ],
  32,
  "(((x)+(#a))=((x)+(0)))=>((((x)+(#a))=(y))=>(((x)+(0))=(y)))"
 ],
 [
  "DEL",
  [
   33
  ],
  33,
  "(((x)+(#a))=(y))=>(((x)+(0))=(y))"
 ],
 [
  "SV",
  [
   10,
   "x"
  ],
  35,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   34
  ],
  34,
  "((x)+(0))=(y)"
 ],
 [
  "Highlight",
  [
   35
  ],
  35,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   29
  ],
  29,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "Highlight",
  [
   22
  ],
  22,
  "((x)+(#a))=(y)"
 ],
 [
  "SV",
  [
   5,
   "(x)+(0)"
  ],
  36,
  "Ay((((x)+(0))=(y))=>((P[(x)+(0)])=>(P[y])))"
 ],
 [
  "SV",
  [
   36,
   "x"
  ],
  37,
  "(((x)+(0))=(x))=>((P[(x)+(0)])=>(P[x]))"
 ],
 [
  "DEL",
  [
   36
  ],
  36,
  "Ay((((x)+(0))=(y))=>((P[(x)+(0)])=>(P[y])))"
 ],
 [
  "S",
  [
   37,
   "P",
   "(@)=(y)"
  ],
  38,
  "(((x)+(0))=(x))=>((((x)+(0))=(y))=>((x)=(y)))"
 ],
 [
  "DEL",
  [
   37
  ],
  37,
  "(((x)+(0))=(x))=>((P[(x)+(0)])=>(P[x]))"
 ],
 [
  "MP",
  [
   38,
   35
  ],
  39,
  "(((x)+(0))=(y))=>((x)=(y))"
 ],
 [
  "MP",
  [
   39,
   34
  ],
  40,
  "(x)=(y)"
 ],
 [
  "DEL",
  [
   38
  ],
  38,
  "(((x)+(0))=(x))=>((((x)+(0))=(y))=>((x)=(y)))"
 ],
 [
  "DEL",
  [
   39
  ],
  39,
  "(((x)+(0))=(y))=>((x)=(y))"
 ],
 [
  "MP",
  [
   16,
   40
  ],
  41,
  "F"
 ],
 [
  "DT",
  [
   23,
   41
  ],
  42,
  "((#a)=(0))=>(F)"
 ],
 [
  "Highlight",
  [
   34
  ],
  34,
  "((x)+(0))=(y)"
 ],
 [
  "Highlight",
  [
   35
  ],
  35,
  "((x)+(0))=(x)"
 ],
 [
  "Quote",
  [
   "nonzero_is_successor"
  ],
  43,
  "Ax(((x)!=(0))=>(Ey((x)=(S(y)))))"
 ],
 [
  "SV",
  [
   43,
   "#a"
  ],
  44,
  "((#a)!=(0))=>(Ey((#a)=(S(y))))"
 ],
 [
  "Rewrite",
  [
   42,
   "(#a)!=(0)"
  ],
  45,
  "(#a)!=(0)"
 ],
 [
  "MP",
  [
   44,
   45
  ],
  46,
  "Ey((#a)=(S(y)))"
 ],
 [
  "SV",
  [
   46,
   "#b"
  ],
  47,
  "(#a)=(S(#b))"
 ],
 [
  "SV",
  [
   4,
   "(x)+(#a)"
  ],
  48,
  "((x)+(#a))=((x)+(#a))"
 ],
 [
  "SV",
  [
   5,
   "#a"
  ],
  49,
  "Ay(((#a)=(y))=>((P[#a])=>(P[y])))"
 ],
 [
  "SV",
  [
   49,
   "S(#b)"
  ],
  50,
  "((#a)=(S(#b)))=>((P[#a])=>(P[S(#b)]))"
 ],
 [
  "DEL",
  [
   49
  ],
  49,
  "Ay(((#a)=(y))=>((P[#a])=>(P[y])))"
 ],
 [
  "S",
  [
   50,
   "P",
   "((x)+(#a))=((x)+(@))"
  ],
  51,
  "((#a)=(S(#b)))=>((((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(S(#b)))))"
 ],
 [
  "DEL",
  [
   50
  ],
  50,
  "((#a)=(S(#b)))=>((P[#a])=>(P[S(#b)]))"
 ],
 [
  "MP",
  [
   51,
   47
  ],
  52,
  "(((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(S(#b))))"
 ],
 [
  "MP",
  [
   52,
   48
  ],
  53,
  "((x)+(#a))=((x)+(S(#b)))"
 ],
 [
  "DEL",
  [
   48
  ],
  48,
  "((x)+(#a))=((x)+(#a))"
 ],
 [
  "DEL",
  [
   51
  ],
  51,
  "((#a)=(S(#b)))=>((((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(S(#b)))))"
 ],
 [
  "DEL",
  [
   52
  ],
  52,
  "(((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(S(#b))))"
 ],
 [
  "Highlight",
  [
   53
  ],
  53,
  "((x)+(#a))=((x)+(S(#b)))"
 ],
 [
  "Highlight",
  [
   22
  ],
  22,
  "((x)+(#a))=(y)"
 ],
 [
  "SV",
  [
   5,
   "(x)+(#a)"
  ],
  54,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "SV",
  [
   54,
   "(x)+(S(#b))"
  ],
  55,
  "(((x)+(#a))=((x)+(S(#b))))=>((P[(x)+(#a)])=>(P[(x)+(S(#b))]))"
 ],
 [
  "DEL",
  [
   54
  ],
  54,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "S",
  [
   55,
   "P",
   "(@)=(y)"
  ],
  56,
  "(((x)+(#a))=((x)+(S(#b))))=>((((x)+(#a))=(y))=>(((x)+(S(#b)))=(y)))"
 ],
 [
  "DEL",
  [
   55
  ],
  55,
  "(((x)+(#a))=((x)+(S(#b))))=>((P[(x)+(#a)])=>(P[(x)+(S(#b))]))"
 ],
 [
  "MP",
  [
   56,
   53
  ],
  57,
  "(((x)+(#a))=(y))=>(((x)+(S(#b)))=(y))"
 ],
 [
  "MP",
  [
   57,
   22
  ],
  58,
  "((x)+(S(#b)))=(y)"
 ],
 [
  "DEL",
  [
   56
  ],
  56,
  "(((x)+(#a))=((x)+(S(#b))))=>((((x)+(#a))=(y))=>(((x)+(S(#b)))=(y)))"
 ],
 [
  "DEL",
  [
   57
  ],
  57,
  "(((x)+(#a))=(y))=>(((x)+(S(#b)))=(y))"
 ],
 [
  "Highlight",
  [
   53
  ],
  53,
  "((x)+(#a))=((x)+(S(#b)))"
 ],
 [
  "Highlight",
  [
   22
  ],
  22,
  "((x)+(#a))=(y)"
 ],
 [
  "Highlight",
  [
   58
  ],
  58,
  "((x)+(S(#b)))=(y)"
 ],
 [
  "GE",
  [
   58,
   "Eb(((x)+(S(b)))=(y))"
  ],
  59,
  "Eb(((x)+(S(b)))=(y))"
 ],
 [
  "Rewrite",
  [
   59,
   "(x)<(y)"
  ],
  60,
  "(x)<(y)"
 ],
 [
  "Quote",
  [
   "or_implies"
  ],
  61,
  "((P)||(Q))=>(((P)=>(R))=>(((Q)=>(R))=>(R)))"
 ],
 [
  "Quote",
  [
   "or_introduction1"
  ],
  62,
  "(P)=>((P)||(Q))"
 ],
 [
  "S",
  [
   62,
   "P",
   "(x)<(y)"
  ],
  63,
  "((x)<(y))=>(((x)<(y))||(Q))"
 ],
 [
  "S",
  [
   63,
   "Q",
   "(y)<(x)"
  ],
  64,
  "((x)<(y))=>(((x)<(y))||((y)<(x)))"
 ],
 [
  "MP",
  [
   64,
   60
  ],
  65,
  "((x)<(y))||((y)<(x))"
 ],
 [
  "DT",
  [
   20,
   65
  ],
  66,
  "((x)<=(y))=>(((x)<(y))||((y)<(x)))"
 ],
 [
  "DT",
  [
   15,
   66
  ],
  67,
  "((x)!=(y))=>(((x)<=(y))=>(((x)<(y))||((y)<(x))))"
 ],
 [
  "G",
  [
   67,
   "y"
  ],
  68,
  "Ay(((x)!=(y))=>(((x)<=(y))=>(((x)<(y))||((y)<(x)))))"
 ],
 [
  "G",
  [
   68,
   "x"
  ],
  69,
  "Ax(Ay(((x)!=(y))=>(((x)<=(y))=>(((x)<(y))||((y)<(x))))))"
 ],
 [
  "SV",
  [
   69,
   "y"
  ],
  70,
  "Ay0(((y)!=(y0))=>(((y)<=(y0))=>(((y)<(y0))||((y0)<(y)))))"
 ],
 [
  "SV",
  [
   70,
   "x"
  ],
  71,
  "((y)!=(x))=>(((y)<=(x))=>(((y)<(x))||((x)<(y))))"
 ],
 [
  "SubRelation",
  [
   71,
   "!=",
   4
  ],
  72,
  "(((y)=(x))=>(F))=>(((y)<=(x))=>(((y)<(x))||((x)<(y))))"
 ],
 [
  "Assume",
  [
   "(y)=(x)"
  ],
  73,
  "(y)=(x)"
 ],
 [
  "Highlight",
  [
   73
  ],
  73,
  "(y)=(x)"
 ],
 [
  "SV",
  [
   5,
   "y"
  ],
  74,
  "Ay0(((y)=(y0))=>((P[y])=>(P[y0])))"
 ],
 [
  "SV",
  [
   74,
   "x"
  ],
  75,
  "((y)=(x))=>((P[y])=>(P[x]))"
 ],
 [
  "DEL",
  [
   74
  ],
  74,
  "Ay0(((y)=(y0))=>((P[y])=>(P[y0])))"
 ],
 [
  "S",
  [
   75,
   "P",
   "(@)=(y)"
  ],
  76,
  "((y)=(x))=>(((y)=(y))=>((x)=(y)))"
 ],
 [
  "DEL",
  [
   75
  ],
  75,
  "((y)=(x))=>((P[y])=>(P[x]))"
 ],
 [
  "SV",
  [
   4,
   "y"
  ],
  77,
  "(y)=(y)"
 ],
 [
  "MP",
  [
   76,
   73
  ],
  78,
  "((y)=(y))=>((x)=(y))"
 ],
 [
  "MP",
  [
   78,
   77
  ],
  79,
  "(x)=(y)"
 ],
 [
  "DEL",
  [
   76
  ],
  76,
  "((y)=(x))=>(((y)=(y))=>((x)=(y)))"
 ],
 [
  "DEL",
  [
   77
  ],
  77,
  "(y)=(y)"
 ],
 [
  "DEL",
  [
   78
  ],
  78,
  "((y)=(y))=>((x)=(y))"
 ],
 [
  "Highlight",
  [
   58
  ],
  58,
  "((x)+(S(#b)))=(y)"
 ],
 [
  "MP",
  [
   16,
   79
  ],
  80,
  "F"
 ],
 [
  "DT",
  [
   73,
   80
  ],
  81,
  "((y)=(x))=>(F)"
 ],
 [
  "MP",
  [
   72,
   81
  ],
  82,
  "((y)<=(x))=>(((y)<(x))||((x)<(y)))"
 ],
 [
  "Assume",
  [
   "(y)<=(x)"
  ],
  83,
  "(y)<=(x)"
 ],
 [
  "MP",
  [
   82,
   83
  ],
  84,
  "((y)<(x))||((x)<(y))"
 ],
 [
  "Quote",
  [
   "or_commutes"
  ],
  85,
  "((P)||(Q))=>((Q)||(P))"
 ],
 [
  "S",
  [
   85,
   "P",
   "(y)<(x)"
  ],
  86,
  "(((y)<(x))||(Q))=>((Q)||((y)<(x)))"
 ],
 [
  "S",
  [
   86,
   "Q",
   "(x)<(y)"
  ],
  87,
  "(((y)<(x))||((x)<(y)))=>(((x)<(y))||((y)<(x)))"
 ],
 [
  "MP",
  [
   87,
   84
  ],
  88,
  "((x)<(y))||((y)<(x))"
 ],
 [
  "DT",
  [
   83,
   88
  ],
  89,
  "((y)<=(x))=>(((x)<(y))||((y)<(x)))"
 ],
 [
  "S",
  [
   61,
   "P",
   "(x)<=(y)"
  ],
  90,
  "(((x)<=(y))||(Q))=>((((x)<=(y))=>(R))=>(((Q)=>(R))=>(R)))"
 ],
 [
  "S",
  [
   90,
   "Q",
   "(y)<=(x)"
  ],
  91,
  "(((x)<=(y))||((y)<=(x)))=>((((x)<=(y))=>(R))=>((((y)<=(x))=>(R))=>(R)))"
 ],
 [
  "S",
  [
   91,
   "R",
   "((x)<(y))||((y)<(x))"
  ],
  92,
  "(((x)<=(y))||((y)<=(x)))=>((((x)<=(y))=>(((x)<(y))||((y)<(x))))=>((((y)<=(x))=>(((x)<(y))||((y)<(x))))=>(((x)<(y))||((y)<(x)))))"
 ],
 [
  "MP",
  [
   92,
   19
  ],
  93,
  "(((x)<=(y))=>(((x)<(y))||((y)<(x))))=>((((y)<=(x))=>(((x)<(y))||((y)<(x))))=>(((x)<(y))||((y)<(x))))"
 ],
 [
  "MP",
  [
   93,
   66
  ],
  94,
  "(((y)<=(x))=>(((x)<(y))||((y)<(x))))=>(((x)<(y))||((y)<(x)))"
 ],
 [
  "MP",
  [
   94,
   89
  ],
  95,
  "((x)<(y))||((y)<(x))"
 ],
 [
  "DT",
  [
   15,
   95
  ],
  96,
  "((x)!=(y))=>(((x)<(y))||((y)<(x)))"
 ],
 [
  "G",
  [
   96,
   "y"
  ],
  97,
  "Ay(((x)!=(y))=>(((x)<(y))||((y)<(x))))"
 ],
 [
  "G",
  [
   97,
   "x"
  ],
  98,
  "Ax(Ay(((x)!=(y))=>(((x)<(y))||((y)<(x)))))"
 ]
];