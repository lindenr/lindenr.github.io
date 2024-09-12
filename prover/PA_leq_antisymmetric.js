window.requiredModules_leq_antisymmetric = ["and_elimination1", "and_elimination2", "addition_associates", "addition_injective", "add_to_0"];
window.proof_leq_antisymmetric = [
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
   "((x)<=(y))&&((y)<=(x))"
  ],
  15,
  "((x)<=(y))&&((y)<=(x))"
 ],
 [
  "Quote",
  [
   "and_elimination1"
  ],
  16,
  "((P)&&(Q))=>(P)"
 ],
 [
  "Quote",
  [
   "and_elimination2"
  ],
  17,
  "((P)&&(Q))=>(Q)"
 ],
 [
  "S",
  [
   16,
   "P",
   "(x)<=(y)"
  ],
  18,
  "(((x)<=(y))&&(Q))=>((x)<=(y))"
 ],
 [
  "S",
  [
   18,
   "Q",
   "(y)<=(x)"
  ],
  19,
  "(((x)<=(y))&&((y)<=(x)))=>((x)<=(y))"
 ],
 [
  "MP",
  [
   19,
   15
  ],
  20,
  "(x)<=(y)"
 ],
 [
  "S",
  [
   17,
   "P",
   "(x)<=(y)"
  ],
  21,
  "(((x)<=(y))&&(Q))=>(Q)"
 ],
 [
  "S",
  [
   21,
   "Q",
   "(y)<=(x)"
  ],
  22,
  "(((x)<=(y))&&((y)<=(x)))=>((y)<=(x))"
 ],
 [
  "MP",
  [
   22,
   15
  ],
  23,
  "(y)<=(x)"
 ],
 [
  "SubRelation",
  [
   20,
   "<=",
   3
  ],
  24,
  "Ex0(((x)+(x0))=(y))"
 ],
 [
  "SubRelation",
  [
   23,
   "<=",
   3
  ],
  25,
  "Ex0(((y)+(x0))=(x))"
 ],
 [
  "SV",
  [
   24,
   "#a"
  ],
  26,
  "((x)+(#a))=(y)"
 ],
 [
  "SV",
  [
   25,
   "#b"
  ],
  27,
  "((y)+(#b))=(x)"
 ],
 [
  "SV",
  [
   4,
   "((x)+(#a))+(#b)"
  ],
  28,
  "(((x)+(#a))+(#b))=(((x)+(#a))+(#b))"
 ],
 [
  "SV",
  [
   5,
   "(x)+(#a)"
  ],
  29,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "SV",
  [
   29,
   "y"
  ],
  30,
  "(((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y]))"
 ],
 [
  "DEL",
  [
   29
  ],
  29,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "S",
  [
   30,
   "P",
   "(((x)+(#a))+(#b))=((@)+(#b))"
  ],
  31,
  "(((x)+(#a))=(y))=>(((((x)+(#a))+(#b))=(((x)+(#a))+(#b)))=>((((x)+(#a))+(#b))=((y)+(#b))))"
 ],
 [
  "DEL",
  [
   30
  ],
  30,
  "(((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y]))"
 ],
 [
  "MP",
  [
   31,
   26
  ],
  32,
  "((((x)+(#a))+(#b))=(((x)+(#a))+(#b)))=>((((x)+(#a))+(#b))=((y)+(#b)))"
 ],
 [
  "MP",
  [
   32,
   28
  ],
  33,
  "(((x)+(#a))+(#b))=((y)+(#b))"
 ],
 [
  "DEL",
  [
   28
  ],
  28,
  "(((x)+(#a))+(#b))=(((x)+(#a))+(#b))"
 ],
 [
  "DEL",
  [
   31
  ],
  31,
  "(((x)+(#a))=(y))=>(((((x)+(#a))+(#b))=(((x)+(#a))+(#b)))=>((((x)+(#a))+(#b))=((y)+(#b))))"
 ],
 [
  "DEL",
  [
   32
  ],
  32,
  "((((x)+(#a))+(#b))=(((x)+(#a))+(#b)))=>((((x)+(#a))+(#b))=((y)+(#b)))"
 ],
 [
  "Highlight",
  [
   27
  ],
  27,
  "((y)+(#b))=(x)"
 ],
 [
  "Highlight",
  [
   33
  ],
  33,
  "(((x)+(#a))+(#b))=((y)+(#b))"
 ],
 [
  "SV",
  [
   5,
   "(y)+(#b)"
  ],
  34,
  "Ay0((((y)+(#b))=(y0))=>((P[(y)+(#b)])=>(P[y0])))"
 ],
 [
  "SV",
  [
   34,
   "x"
  ],
  35,
  "(((y)+(#b))=(x))=>((P[(y)+(#b)])=>(P[x]))"
 ],
 [
  "DEL",
  [
   34
  ],
  34,
  "Ay0((((y)+(#b))=(y0))=>((P[(y)+(#b)])=>(P[y0])))"
 ],
 [
  "S",
  [
   35,
   "P",
   "(((x)+(#a))+(#b))=(@)"
  ],
  36,
  "(((y)+(#b))=(x))=>(((((x)+(#a))+(#b))=((y)+(#b)))=>((((x)+(#a))+(#b))=(x)))"
 ],
 [
  "DEL",
  [
   35
  ],
  35,
  "(((y)+(#b))=(x))=>((P[(y)+(#b)])=>(P[x]))"
 ],
 [
  "MP",
  [
   36,
   27
  ],
  37,
  "((((x)+(#a))+(#b))=((y)+(#b)))=>((((x)+(#a))+(#b))=(x))"
 ],
 [
  "MP",
  [
   37,
   33
  ],
  38,
  "(((x)+(#a))+(#b))=(x)"
 ],
 [
  "DEL",
  [
   37
  ],
  37,
  "((((x)+(#a))+(#b))=((y)+(#b)))=>((((x)+(#a))+(#b))=(x))"
 ],
 [
  "DEL",
  [
   36
  ],
  36,
  "(((y)+(#b))=(x))=>(((((x)+(#a))+(#b))=((y)+(#b)))=>((((x)+(#a))+(#b))=(x)))"
 ],
 [
  "Highlight",
  [
   33
  ],
  33,
  "(((x)+(#a))+(#b))=((y)+(#b))"
 ],
 [
  "Highlight",
  [
   27
  ],
  27,
  "((y)+(#b))=(x)"
 ],
 [
  "Quote",
  [
   "addition_associates"
  ],
  39,
  "Ax(Ay(Az((((x)+(y))+(z))=((x)+((y)+(z))))))"
 ],
 [
  "SV",
  [
   39,
   "x"
  ],
  40,
  "Ay(Az((((x)+(y))+(z))=((x)+((y)+(z)))))"
 ],
 [
  "SV",
  [
   40,
   "#a"
  ],
  41,
  "Az((((x)+(#a))+(z))=((x)+((#a)+(z))))"
 ],
 [
  "SV",
  [
   41,
   "#b"
  ],
  42,
  "(((x)+(#a))+(#b))=((x)+((#a)+(#b)))"
 ],
 [
  "Highlight",
  [
   38
  ],
  38,
  "(((x)+(#a))+(#b))=(x)"
 ],
 [
  "Highlight",
  [
   42
  ],
  42,
  "(((x)+(#a))+(#b))=((x)+((#a)+(#b)))"
 ],
 [
  "SV",
  [
   5,
   "((x)+(#a))+(#b)"
  ],
  43,
  "Ay(((((x)+(#a))+(#b))=(y))=>((P[((x)+(#a))+(#b)])=>(P[y])))"
 ],
 [
  "SV",
  [
   43,
   "x"
  ],
  44,
  "((((x)+(#a))+(#b))=(x))=>((P[((x)+(#a))+(#b)])=>(P[x]))"
 ],
 [
  "DEL",
  [
   43
  ],
  43,
  "Ay(((((x)+(#a))+(#b))=(y))=>((P[((x)+(#a))+(#b)])=>(P[y])))"
 ],
 [
  "S",
  [
   44,
   "P",
   "(@)=((x)+((#a)+(#b)))"
  ],
  45,
  "((((x)+(#a))+(#b))=(x))=>(((((x)+(#a))+(#b))=((x)+((#a)+(#b))))=>((x)=((x)+((#a)+(#b)))))"
 ],
 [
  "DEL",
  [
   44
  ],
  44,
  "((((x)+(#a))+(#b))=(x))=>((P[((x)+(#a))+(#b)])=>(P[x]))"
 ],
 [
  "MP",
  [
   45,
   38
  ],
  46,
  "((((x)+(#a))+(#b))=((x)+((#a)+(#b))))=>((x)=((x)+((#a)+(#b))))"
 ],
 [
  "MP",
  [
   46,
   42
  ],
  47,
  "(x)=((x)+((#a)+(#b)))"
 ],
 [
  "DEL",
  [
   45
  ],
  45,
  "((((x)+(#a))+(#b))=(x))=>(((((x)+(#a))+(#b))=((x)+((#a)+(#b))))=>((x)=((x)+((#a)+(#b)))))"
 ],
 [
  "DEL",
  [
   46
  ],
  46,
  "((((x)+(#a))+(#b))=((x)+((#a)+(#b))))=>((x)=((x)+((#a)+(#b))))"
 ],
 [
  "Highlight",
  [
   42
  ],
  42,
  "(((x)+(#a))+(#b))=((x)+((#a)+(#b)))"
 ],
 [
  "Highlight",
  [
   38
  ],
  38,
  "(((x)+(#a))+(#b))=(x)"
 ],
 [
  "Highlight",
  [
   47
  ],
  47,
  "(x)=((x)+((#a)+(#b)))"
 ],
 [
  "Quote",
  [
   "addition_injective"
  ],
  48,
  "Ax(Aa(Ab((((x)+(a))=((x)+(b)))=>((a)=(b)))))"
 ],
 [
  "SV",
  [
   48,
   "x"
  ],
  49,
  "Aa(Ab((((x)+(a))=((x)+(b)))=>((a)=(b))))"
 ],
 [
  "SV",
  [
   49,
   "(#a)+(#b)"
  ],
  50,
  "Ab((((x)+((#a)+(#b)))=((x)+(b)))=>(((#a)+(#b))=(b)))"
 ],
 [
  "SV",
  [
   50,
   "0"
  ],
  51,
  "(((x)+((#a)+(#b)))=((x)+(0)))=>(((#a)+(#b))=(0))"
 ],
 [
  "SV",
  [
   10,
   "x"
  ],
  52,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   52
  ],
  52,
  "((x)+(0))=(x)"
 ],
 [
  "SV",
  [
   5,
   "x"
  ],
  53,
  "Ay(((x)=(y))=>((P[x])=>(P[y])))"
 ],
 [
  "SV",
  [
   53,
   "(x)+((#a)+(#b))"
  ],
  54,
  "((x)=((x)+((#a)+(#b))))=>((P[x])=>(P[(x)+((#a)+(#b))]))"
 ],
 [
  "DEL",
  [
   53
  ],
  53,
  "Ay(((x)=(y))=>((P[x])=>(P[y])))"
 ],
 [
  "S",
  [
   54,
   "P",
   "((x)+(0))=(@)"
  ],
  55,
  "((x)=((x)+((#a)+(#b))))=>((((x)+(0))=(x))=>(((x)+(0))=((x)+((#a)+(#b)))))"
 ],
 [
  "DEL",
  [
   54
  ],
  54,
  "((x)=((x)+((#a)+(#b))))=>((P[x])=>(P[(x)+((#a)+(#b))]))"
 ],
 [
  "MP",
  [
   55,
   47
  ],
  56,
  "(((x)+(0))=(x))=>(((x)+(0))=((x)+((#a)+(#b))))"
 ],
 [
  "MP",
  [
   56,
   52
  ],
  57,
  "((x)+(0))=((x)+((#a)+(#b)))"
 ],
 [
  "DEL",
  [
   56
  ],
  56,
  "(((x)+(0))=(x))=>(((x)+(0))=((x)+((#a)+(#b))))"
 ],
 [
  "DEL",
  [
   55
  ],
  55,
  "((x)=((x)+((#a)+(#b))))=>((((x)+(0))=(x))=>(((x)+(0))=((x)+((#a)+(#b)))))"
 ],
 [
  "Highlight",
  [
   52
  ],
  52,
  "((x)+(0))=(x)"
 ],
 [
  "Highlight",
  [
   47
  ],
  47,
  "(x)=((x)+((#a)+(#b)))"
 ],
 [
  "Highlight",
  [
   51
  ],
  51,
  "(((x)+((#a)+(#b)))=((x)+(0)))=>(((#a)+(#b))=(0))"
 ],
 [
  "Highlight",
  [
   57
  ],
  57,
  "((x)+(0))=((x)+((#a)+(#b)))"
 ],
 [
  "SV",
  [
   5,
   "(x)+(0)"
  ],
  58,
  "Ay((((x)+(0))=(y))=>((P[(x)+(0)])=>(P[y])))"
 ],
 [
  "SV",
  [
   58,
   "(x)+((#a)+(#b))"
  ],
  59,
  "(((x)+(0))=((x)+((#a)+(#b))))=>((P[(x)+(0)])=>(P[(x)+((#a)+(#b))]))"
 ],
 [
  "DEL",
  [
   58
  ],
  58,
  "Ay((((x)+(0))=(y))=>((P[(x)+(0)])=>(P[y])))"
 ],
 [
  "S",
  [
   59,
   "P",
   "(@)=((x)+(0))"
  ],
  60,
  "(((x)+(0))=((x)+((#a)+(#b))))=>((((x)+(0))=((x)+(0)))=>(((x)+((#a)+(#b)))=((x)+(0))))"
 ],
 [
  "DEL",
  [
   59
  ],
  59,
  "(((x)+(0))=((x)+((#a)+(#b))))=>((P[(x)+(0)])=>(P[(x)+((#a)+(#b))]))"
 ],
 [
  "SV",
  [
   4,
   "(x)+(0)"
  ],
  61,
  "((x)+(0))=((x)+(0))"
 ],
 [
  "MP",
  [
   60,
   57
  ],
  62,
  "(((x)+(0))=((x)+(0)))=>(((x)+((#a)+(#b)))=((x)+(0)))"
 ],
 [
  "MP",
  [
   62,
   61
  ],
  63,
  "((x)+((#a)+(#b)))=((x)+(0))"
 ],
 [
  "DEL",
  [
   60
  ],
  60,
  "(((x)+(0))=((x)+((#a)+(#b))))=>((((x)+(0))=((x)+(0)))=>(((x)+((#a)+(#b)))=((x)+(0))))"
 ],
 [
  "DEL",
  [
   61
  ],
  61,
  "((x)+(0))=((x)+(0))"
 ],
 [
  "DEL",
  [
   62
  ],
  62,
  "(((x)+(0))=((x)+(0)))=>(((x)+((#a)+(#b)))=((x)+(0)))"
 ],
 [
  "Highlight",
  [
   63
  ],
  63,
  "((x)+((#a)+(#b)))=((x)+(0))"
 ],
 [
  "Highlight",
  [
   57
  ],
  57,
  "((x)+(0))=((x)+((#a)+(#b)))"
 ],
 [
  "MP",
  [
   51,
   63
  ],
  64,
  "((#a)+(#b))=(0)"
 ],
 [
  "Highlight",
  [
   51
  ],
  51,
  "(((x)+((#a)+(#b)))=((x)+(0)))=>(((#a)+(#b))=(0))"
 ],
 [
  "Highlight",
  [
   63
  ],
  63,
  "((x)+((#a)+(#b)))=((x)+(0))"
 ],
 [
  "Quote",
  [
   "add_to_0"
  ],
  65,
  "Ax(Ay((((x)+(y))=(0))=>((x)=(0))))"
 ],
 [
  "SV",
  [
   65,
   "#a"
  ],
  66,
  "Ay((((#a)+(y))=(0))=>((#a)=(0)))"
 ],
 [
  "SV",
  [
   66,
   "#b"
  ],
  67,
  "(((#a)+(#b))=(0))=>((#a)=(0))"
 ],
 [
  "MP",
  [
   67,
   64
  ],
  68,
  "(#a)=(0)"
 ],
 [
  "SV",
  [
   4,
   "(x)+(#a)"
  ],
  69,
  "((x)+(#a))=((x)+(#a))"
 ],
 [
  "SV",
  [
   5,
   "#a"
  ],
  70,
  "Ay(((#a)=(y))=>((P[#a])=>(P[y])))"
 ],
 [
  "SV",
  [
   70,
   "0"
  ],
  71,
  "((#a)=(0))=>((P[#a])=>(P[0]))"
 ],
 [
  "DEL",
  [
   70
  ],
  70,
  "Ay(((#a)=(y))=>((P[#a])=>(P[y])))"
 ],
 [
  "S",
  [
   71,
   "P",
   "((x)+(#a))=((x)+(@))"
  ],
  72,
  "((#a)=(0))=>((((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0))))"
 ],
 [
  "DEL",
  [
   71
  ],
  71,
  "((#a)=(0))=>((P[#a])=>(P[0]))"
 ],
 [
  "MP",
  [
   72,
   68
  ],
  73,
  "(((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0)))"
 ],
 [
  "MP",
  [
   73,
   69
  ],
  74,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "DEL",
  [
   69
  ],
  69,
  "((x)+(#a))=((x)+(#a))"
 ],
 [
  "DEL",
  [
   72
  ],
  72,
  "((#a)=(0))=>((((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0))))"
 ],
 [
  "DEL",
  [
   73
  ],
  73,
  "(((x)+(#a))=((x)+(#a)))=>(((x)+(#a))=((x)+(0)))"
 ],
 [
  "Highlight",
  [
   26
  ],
  26,
  "((x)+(#a))=(y)"
 ],
 [
  "Highlight",
  [
   74
  ],
  74,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "SV",
  [
   5,
   "(x)+(#a)"
  ],
  75,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "SV",
  [
   75,
   "y"
  ],
  76,
  "(((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y]))"
 ],
 [
  "DEL",
  [
   75
  ],
  75,
  "Ay((((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y])))"
 ],
 [
  "S",
  [
   76,
   "P",
   "(@)=((x)+(0))"
  ],
  77,
  "(((x)+(#a))=(y))=>((((x)+(#a))=((x)+(0)))=>((y)=((x)+(0))))"
 ],
 [
  "DEL",
  [
   76
  ],
  76,
  "(((x)+(#a))=(y))=>((P[(x)+(#a)])=>(P[y]))"
 ],
 [
  "MP",
  [
   77,
   26
  ],
  78,
  "(((x)+(#a))=((x)+(0)))=>((y)=((x)+(0)))"
 ],
 [
  "MP",
  [
   78,
   74
  ],
  79,
  "(y)=((x)+(0))"
 ],
 [
  "DEL",
  [
   77
  ],
  77,
  "(((x)+(#a))=(y))=>((((x)+(#a))=((x)+(0)))=>((y)=((x)+(0))))"
 ],
 [
  "DEL",
  [
   78
  ],
  78,
  "(((x)+(#a))=((x)+(0)))=>((y)=((x)+(0)))"
 ],
 [
  "Highlight",
  [
   74
  ],
  74,
  "((x)+(#a))=((x)+(0))"
 ],
 [
  "Highlight",
  [
   26
  ],
  26,
  "((x)+(#a))=(y)"
 ],
 [
  "Highlight",
  [
   79
  ],
  79,
  "(y)=((x)+(0))"
 ],
 [
  "Highlight",
  [
   52
  ],
  52,
  "((x)+(0))=(x)"
 ],
 [
  "SV",
  [
   5,
   "(x)+(0)"
  ],
  80,
  "Ay((((x)+(0))=(y))=>((P[(x)+(0)])=>(P[y])))"
 ],
 [
  "SV",
  [
   80,
   "x"
  ],
  81,
  "(((x)+(0))=(x))=>((P[(x)+(0)])=>(P[x]))"
 ],
 [
  "DEL",
  [
   80
  ],
  80,
  "Ay((((x)+(0))=(y))=>((P[(x)+(0)])=>(P[y])))"
 ],
 [
  "S",
  [
   81,
   "P",
   "(y)=(@)"
  ],
  82,
  "(((x)+(0))=(x))=>(((y)=((x)+(0)))=>((y)=(x)))"
 ],
 [
  "DEL",
  [
   81
  ],
  81,
  "(((x)+(0))=(x))=>((P[(x)+(0)])=>(P[x]))"
 ],
 [
  "MP",
  [
   82,
   52
  ],
  83,
  "((y)=((x)+(0)))=>((y)=(x))"
 ],
 [
  "MP",
  [
   83,
   79
  ],
  84,
  "(y)=(x)"
 ],
 [
  "DEL",
  [
   83
  ],
  83,
  "((y)=((x)+(0)))=>((y)=(x))"
 ],
 [
  "DEL",
  [
   82
  ],
  82,
  "(((x)+(0))=(x))=>(((y)=((x)+(0)))=>((y)=(x)))"
 ],
 [
  "Highlight",
  [
   84
  ],
  84,
  "(y)=(x)"
 ],
 [
  "Highlight",
  [
   79
  ],
  79,
  "(y)=((x)+(0))"
 ],
 [
  "Highlight",
  [
   52
  ],
  52,
  "((x)+(0))=(x)"
 ],
 [
  "SV",
  [
   5,
   "y"
  ],
  85,
  "Ay0(((y)=(y0))=>((P[y])=>(P[y0])))"
 ],
 [
  "SV",
  [
   85,
   "x"
  ],
  86,
  "((y)=(x))=>((P[y])=>(P[x]))"
 ],
 [
  "DEL",
  [
   85
  ],
  85,
  "Ay0(((y)=(y0))=>((P[y])=>(P[y0])))"
 ],
 [
  "S",
  [
   86,
   "P",
   "(@)=(y)"
  ],
  87,
  "((y)=(x))=>(((y)=(y))=>((x)=(y)))"
 ],
 [
  "DEL",
  [
   86
  ],
  86,
  "((y)=(x))=>((P[y])=>(P[x]))"
 ],
 [
  "SV",
  [
   4,
   "y"
  ],
  88,
  "(y)=(y)"
 ],
 [
  "MP",
  [
   87,
   84
  ],
  89,
  "((y)=(y))=>((x)=(y))"
 ],
 [
  "MP",
  [
   89,
   88
  ],
  90,
  "(x)=(y)"
 ],
 [
  "DEL",
  [
   87
  ],
  87,
  "((y)=(x))=>(((y)=(y))=>((x)=(y)))"
 ],
 [
  "DEL",
  [
   88
  ],
  88,
  "(y)=(y)"
 ],
 [
  "DEL",
  [
   89
  ],
  89,
  "((y)=(y))=>((x)=(y))"
 ],
 [
  "Highlight",
  [
   84
  ],
  84,
  "(y)=(x)"
 ],
 [
  "DT",
  [
   15,
   90
  ],
  91,
  "(((x)<=(y))&&((y)<=(x)))=>((x)=(y))"
 ],
 [
  "G",
  [
   91,
   "y"
  ],
  92,
  "Ay((((x)<=(y))&&((y)<=(x)))=>((x)=(y)))"
 ],
 [
  "G",
  [
   92,
   "x"
  ],
  93,
  "Ax(Ay((((x)<=(y))&&((y)<=(x)))=>((x)=(y))))"
 ]
];