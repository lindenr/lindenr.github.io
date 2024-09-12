window.requiredModules_multiplication_associates = ["distributivity"];
window.proof_multiplication_associates = [
 [
  "Quote",
  [
   "distributivity"
  ],
  15,
  "Ax(Aa(Ab(((x)*((a)+(b)))=(((x)*(a))+((x)*(b))))))"
 ],
 [
  "SV",
  [
   12,
   "(x)*(y)"
  ],
  16,
  "(((x)*(y))*(0))=(0)"
 ],
 [
  "SV",
  [
   12,
   "y"
  ],
  17,
  "((y)*(0))=(0)"
 ],
 [
  "SV",
  [
   4,
   "(x)*((y)*(0))"
  ],
  18,
  "((x)*((y)*(0)))=((x)*((y)*(0)))"
 ],
 [
  "SV",
  [
   5,
   "(y)*(0)"
  ],
  19,
  "Ay0((((y)*(0))=(y0))=>((P[(y)*(0)])=>(P[y0])))"
 ],
 [
  "SV",
  [
   19,
   "0"
  ],
  20,
  "(((y)*(0))=(0))=>((P[(y)*(0)])=>(P[0]))"
 ],
 [
  "DEL",
  [
   19
  ],
  21,
  "Ay0((((y)*(0))=(y0))=>((P[(y)*(0)])=>(P[y0])))"
 ],
 [
  "S",
  [
   20,
   "P",
   "((x)*((y)*(0)))=((x)*(@))"
  ],
  22,
  "(((y)*(0))=(0))=>((((x)*((y)*(0)))=((x)*((y)*(0))))=>(((x)*((y)*(0)))=((x)*(0))))"
 ],
 [
  "DEL",
  [
   20
  ],
  23,
  "(((y)*(0))=(0))=>((P[(y)*(0)])=>(P[0]))"
 ],
 [
  "MP",
  [
   21,
   17
  ],
  24,
  "(((x)*((y)*(0)))=((x)*((y)*(0))))=>(((x)*((y)*(0)))=((x)*(0)))"
 ],
 [
  "MP",
  [
   22,
   18
  ],
  25,
  "((x)*((y)*(0)))=((x)*(0))"
 ],
 [
  "DEL",
  [
   18
  ],
  26,
  "((x)*((y)*(0)))=((x)*((y)*(0)))"
 ],
 [
  "DEL",
  [
   21
  ],
  27,
  "(((y)*(0))=(0))=>((((x)*((y)*(0)))=((x)*((y)*(0))))=>(((x)*((y)*(0)))=((x)*(0))))"
 ],
 [
  "DEL",
  [
   22
  ],
  28,
  "(((x)*((y)*(0)))=((x)*((y)*(0))))=>(((x)*((y)*(0)))=((x)*(0)))"
 ],
 [
  "SV",
  [
   12,
   "x"
  ],
  29,
  "((x)*(0))=(0)"
 ],
 [
  "SV",
  [
   5,
   "(x)*(0)"
  ],
  30,
  "Ay((((x)*(0))=(y))=>((P[(x)*(0)])=>(P[y])))"
 ],
 [
  "SV",
  [
   25,
   "0"
  ],
  31,
  "(((x)*(0))=(0))=>((P[(x)*(0)])=>(P[0]))"
 ],
 [
  "DEL",
  [
   25
  ],
  32,
  "Ay((((x)*(0))=(y))=>((P[(x)*(0)])=>(P[y])))"
 ],
 [
  "S",
  [
   26,
   "P",
   "((x)*((y)*(0)))=(@)"
  ],
  33,
  "(((x)*(0))=(0))=>((((x)*((y)*(0)))=((x)*(0)))=>(((x)*((y)*(0)))=(0)))"
 ],
 [
  "DEL",
  [
   26
  ],
  34,
  "(((x)*(0))=(0))=>((P[(x)*(0)])=>(P[0]))"
 ],
 [
  "MP",
  [
   27,
   24
  ],
  35,
  "(((x)*((y)*(0)))=((x)*(0)))=>(((x)*((y)*(0)))=(0))"
 ],
 [
  "MP",
  [
   28,
   23
  ],
  36,
  "((x)*((y)*(0)))=(0)"
 ],
 [
  "DEL",
  [
   28
  ],
  37,
  "(((x)*((y)*(0)))=((x)*(0)))=>(((x)*((y)*(0)))=(0))"
 ],
 [
  "DEL",
  [
   27
  ],
  38,
  "(((x)*(0))=(0))=>((((x)*((y)*(0)))=((x)*(0)))=>(((x)*((y)*(0)))=(0)))"
 ],
 [
  "SV",
  [
   5,
   "(x)*((y)*(0))"
  ],
  39,
  "Ay0((((x)*((y)*(0)))=(y0))=>((P[(x)*((y)*(0))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   30,
   "0"
  ],
  40,
  "(((x)*((y)*(0)))=(0))=>((P[(x)*((y)*(0))])=>(P[0]))"
 ],
 [
  "DEL",
  [
   30
  ],
  41,
  "Ay0((((x)*((y)*(0)))=(y0))=>((P[(x)*((y)*(0))])=>(P[y0])))"
 ],
 [
  "S",
  [
   31,
   "P",
   "(@)=((x)*((y)*(0)))"
  ],
  42,
  "(((x)*((y)*(0)))=(0))=>((((x)*((y)*(0)))=((x)*((y)*(0))))=>((0)=((x)*((y)*(0)))))"
 ],
 [
  "DEL",
  [
   31
  ],
  43,
  "(((x)*((y)*(0)))=(0))=>((P[(x)*((y)*(0))])=>(P[0]))"
 ],
 [
  "SV",
  [
   4,
   "(x)*((y)*(0))"
  ],
  44,
  "((x)*((y)*(0)))=((x)*((y)*(0)))"
 ],
 [
  "MP",
  [
   32,
   29
  ],
  45,
  "(((x)*((y)*(0)))=((x)*((y)*(0))))=>((0)=((x)*((y)*(0))))"
 ],
 [
  "MP",
  [
   34,
   33
  ],
  46,
  "(0)=((x)*((y)*(0)))"
 ],
 [
  "SV",
  [
   5,
   "0"
  ],
  47,
  "Ay(((0)=(y))=>((P[0])=>(P[y])))"
 ],
 [
  "SV",
  [
   36,
   "(x)*((y)*(0))"
  ],
  48,
  "((0)=((x)*((y)*(0))))=>((P[0])=>(P[(x)*((y)*(0))]))"
 ],
 [
  "DEL",
  [
   36
  ],
  49,
  "Ay(((0)=(y))=>((P[0])=>(P[y])))"
 ],
 [
  "S",
  [
   37,
   "P",
   "(((x)*(y))*(0))=(@)"
  ],
  50,
  "((0)=((x)*((y)*(0))))=>(((((x)*(y))*(0))=(0))=>((((x)*(y))*(0))=((x)*((y)*(0)))))"
 ],
 [
  "DEL",
  [
   37
  ],
  51,
  "((0)=((x)*((y)*(0))))=>((P[0])=>(P[(x)*((y)*(0))]))"
 ],
 [
  "MP",
  [
   38,
   35
  ],
  52,
  "((((x)*(y))*(0))=(0))=>((((x)*(y))*(0))=((x)*((y)*(0))))"
 ],
 [
  "MP",
  [
   39,
   16
  ],
  53,
  "(((x)*(y))*(0))=((x)*((y)*(0)))"
 ],
 [
  "DEL",
  [
   32
  ],
  54,
  "(((x)*((y)*(0)))=(0))=>((((x)*((y)*(0)))=((x)*((y)*(0))))=>((0)=((x)*((y)*(0)))))"
 ],
 [
  "DEL",
  [
   33
  ],
  55,
  "((x)*((y)*(0)))=((x)*((y)*(0)))"
 ],
 [
  "DEL",
  [
   34
  ],
  56,
  "(((x)*((y)*(0)))=((x)*((y)*(0))))=>((0)=((x)*((y)*(0))))"
 ],
 [
  "DEL",
  [
   35
  ],
  57,
  "(0)=((x)*((y)*(0)))"
 ],
 [
  "DEL",
  [
   38
  ],
  58,
  "((0)=((x)*((y)*(0))))=>(((((x)*(y))*(0))=(0))=>((((x)*(y))*(0))=((x)*((y)*(0)))))"
 ],
 [
  "DEL",
  [
   39
  ],
  59,
  "((((x)*(y))*(0))=(0))=>((((x)*(y))*(0))=((x)*((y)*(0))))"
 ],
 [
  "Assume",
  [
   "(((x)*(y))*(z))=((x)*((y)*(z)))"
  ],
  60,
  "(((x)*(y))*(z))=((x)*((y)*(z)))"
 ],
 [
  "SV",
  [
   13,
   "(x)*(y)"
  ],
  61,
  "Ay0((((x)*(y))*(S(y0)))=((((x)*(y))*(y0))+((x)*(y))))"
 ],
 [
  "SV",
  [
   42,
   "z"
  ],
  62,
  "(((x)*(y))*(S(z)))=((((x)*(y))*(z))+((x)*(y)))"
 ],
 [
  "SV",
  [
   4,
   "(((x)*(y))*(z))+((x)*(y))"
  ],
  63,
  "((((x)*(y))*(z))+((x)*(y)))=((((x)*(y))*(z))+((x)*(y)))"
 ],
 [
  "SV",
  [
   5,
   "((x)*(y))*(z)"
  ],
  64,
  "Ay0(((((x)*(y))*(z))=(y0))=>((P[((x)*(y))*(z)])=>(P[y0])))"
 ],
 [
  "SV",
  [
   45,
   "(x)*((y)*(z))"
  ],
  65,
  "((((x)*(y))*(z))=((x)*((y)*(z))))=>((P[((x)*(y))*(z)])=>(P[(x)*((y)*(z))]))"
 ],
 [
  "DEL",
  [
   45
  ],
  66,
  "Ay0(((((x)*(y))*(z))=(y0))=>((P[((x)*(y))*(z)])=>(P[y0])))"
 ],
 [
  "S",
  [
   46,
   "P",
   "((((x)*(y))*(z))+((x)*(y)))=((@)+((x)*(y)))"
  ],
  67,
  "((((x)*(y))*(z))=((x)*((y)*(z))))=>((((((x)*(y))*(z))+((x)*(y)))=((((x)*(y))*(z))+((x)*(y))))=>(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y)))))"
 ],
 [
  "DEL",
  [
   46
  ],
  68,
  "((((x)*(y))*(z))=((x)*((y)*(z))))=>((P[((x)*(y))*(z)])=>(P[(x)*((y)*(z))]))"
 ],
 [
  "MP",
  [
   47,
   41
  ],
  69,
  "(((((x)*(y))*(z))+((x)*(y)))=((((x)*(y))*(z))+((x)*(y))))=>(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y))))"
 ],
 [
  "MP",
  [
   48,
   44
  ],
  70,
  "((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y)))"
 ],
 [
  "DEL",
  [
   44
  ],
  71,
  "((((x)*(y))*(z))+((x)*(y)))=((((x)*(y))*(z))+((x)*(y)))"
 ],
 [
  "DEL",
  [
   47
  ],
  72,
  "((((x)*(y))*(z))=((x)*((y)*(z))))=>((((((x)*(y))*(z))+((x)*(y)))=((((x)*(y))*(z))+((x)*(y))))=>(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y)))))"
 ],
 [
  "DEL",
  [
   48
  ],
  73,
  "(((((x)*(y))*(z))+((x)*(y)))=((((x)*(y))*(z))+((x)*(y))))=>(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y))))"
 ],
 [
  "SV",
  [
   15,
   "x"
  ],
  74,
  "Aa(Ab(((x)*((a)+(b)))=(((x)*(a))+((x)*(b)))))"
 ],
 [
  "SV",
  [
   50,
   "(y)*(z)"
  ],
  75,
  "Ab(((x)*(((y)*(z))+(b)))=(((x)*((y)*(z)))+((x)*(b))))"
 ],
 [
  "SV",
  [
   51,
   "y"
  ],
  76,
  "((x)*(((y)*(z))+(y)))=(((x)*((y)*(z)))+((x)*(y)))"
 ],
 [
  "SV",
  [
   5,
   "(((x)*(y))*(z))+((x)*(y))"
  ],
  77,
  "Ay0((((((x)*(y))*(z))+((x)*(y)))=(y0))=>((P[(((x)*(y))*(z))+((x)*(y))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   53,
   "((x)*((y)*(z)))+((x)*(y))"
  ],
  78,
  "(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y))))=>((P[(((x)*(y))*(z))+((x)*(y))])=>(P[((x)*((y)*(z)))+((x)*(y))]))"
 ],
 [
  "DEL",
  [
   53
  ],
  79,
  "Ay0((((((x)*(y))*(z))+((x)*(y)))=(y0))=>((P[(((x)*(y))*(z))+((x)*(y))])=>(P[y0])))"
 ],
 [
  "S",
  [
   54,
   "P",
   "(((x)*(y))*(S(z)))=(@)"
  ],
  80,
  "(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y))))=>(((((x)*(y))*(S(z)))=((((x)*(y))*(z))+((x)*(y))))=>((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y)))))"
 ],
 [
  "DEL",
  [
   54
  ],
  81,
  "(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y))))=>((P[(((x)*(y))*(z))+((x)*(y))])=>(P[((x)*((y)*(z)))+((x)*(y))]))"
 ],
 [
  "MP",
  [
   55,
   49
  ],
  82,
  "((((x)*(y))*(S(z)))=((((x)*(y))*(z))+((x)*(y))))=>((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y))))"
 ],
 [
  "MP",
  [
   56,
   43
  ],
  83,
  "(((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y)))"
 ],
 [
  "DEL",
  [
   56
  ],
  84,
  "((((x)*(y))*(S(z)))=((((x)*(y))*(z))+((x)*(y))))=>((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y))))"
 ],
 [
  "DEL",
  [
   55
  ],
  85,
  "(((((x)*(y))*(z))+((x)*(y)))=(((x)*((y)*(z)))+((x)*(y))))=>(((((x)*(y))*(S(z)))=((((x)*(y))*(z))+((x)*(y))))=>((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y)))))"
 ],
 [
  "SV",
  [
   5,
   "(x)*(((y)*(z))+(y))"
  ],
  86,
  "Ay0((((x)*(((y)*(z))+(y)))=(y0))=>((P[(x)*(((y)*(z))+(y))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   58,
   "((x)*((y)*(z)))+((x)*(y))"
  ],
  87,
  "(((x)*(((y)*(z))+(y)))=(((x)*((y)*(z)))+((x)*(y))))=>((P[(x)*(((y)*(z))+(y))])=>(P[((x)*((y)*(z)))+((x)*(y))]))"
 ],
 [
  "DEL",
  [
   58
  ],
  88,
  "Ay0((((x)*(((y)*(z))+(y)))=(y0))=>((P[(x)*(((y)*(z))+(y))])=>(P[y0])))"
 ],
 [
  "S",
  [
   59,
   "P",
   "(@)=((x)*(((y)*(z))+(y)))"
  ],
  89,
  "(((x)*(((y)*(z))+(y)))=(((x)*((y)*(z)))+((x)*(y))))=>((((x)*(((y)*(z))+(y)))=((x)*(((y)*(z))+(y))))=>((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y)))))"
 ],
 [
  "DEL",
  [
   59
  ],
  90,
  "(((x)*(((y)*(z))+(y)))=(((x)*((y)*(z)))+((x)*(y))))=>((P[(x)*(((y)*(z))+(y))])=>(P[((x)*((y)*(z)))+((x)*(y))]))"
 ],
 [
  "SV",
  [
   4,
   "(x)*(((y)*(z))+(y))"
  ],
  91,
  "((x)*(((y)*(z))+(y)))=((x)*(((y)*(z))+(y)))"
 ],
 [
  "MP",
  [
   60,
   52
  ],
  92,
  "(((x)*(((y)*(z))+(y)))=((x)*(((y)*(z))+(y))))=>((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y))))"
 ],
 [
  "MP",
  [
   62,
   61
  ],
  93,
  "(((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y)))"
 ],
 [
  "SV",
  [
   5,
   "((x)*((y)*(z)))+((x)*(y))"
  ],
  94,
  "Ay0(((((x)*((y)*(z)))+((x)*(y)))=(y0))=>((P[((x)*((y)*(z)))+((x)*(y))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   64,
   "(x)*(((y)*(z))+(y))"
  ],
  95,
  "((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y))))=>((P[((x)*((y)*(z)))+((x)*(y))])=>(P[(x)*(((y)*(z))+(y))]))"
 ],
 [
  "DEL",
  [
   64
  ],
  96,
  "Ay0(((((x)*((y)*(z)))+((x)*(y)))=(y0))=>((P[((x)*((y)*(z)))+((x)*(y))])=>(P[y0])))"
 ],
 [
  "S",
  [
   65,
   "P",
   "(((x)*(y))*(S(z)))=(@)"
  ],
  97,
  "((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y))))=>(((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y))))=>((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y)))))"
 ],
 [
  "DEL",
  [
   65
  ],
  98,
  "((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y))))=>((P[((x)*((y)*(z)))+((x)*(y))])=>(P[(x)*(((y)*(z))+(y))]))"
 ],
 [
  "MP",
  [
   66,
   63
  ],
  99,
  "((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y))))=>((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y))))"
 ],
 [
  "MP",
  [
   67,
   57
  ],
  100,
  "(((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y)))"
 ],
 [
  "DEL",
  [
   60
  ],
  101,
  "(((x)*(((y)*(z))+(y)))=(((x)*((y)*(z)))+((x)*(y))))=>((((x)*(((y)*(z))+(y)))=((x)*(((y)*(z))+(y))))=>((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y)))))"
 ],
 [
  "DEL",
  [
   61
  ],
  102,
  "((x)*(((y)*(z))+(y)))=((x)*(((y)*(z))+(y)))"
 ],
 [
  "DEL",
  [
   62
  ],
  103,
  "(((x)*(((y)*(z))+(y)))=((x)*(((y)*(z))+(y))))=>((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y))))"
 ],
 [
  "DEL",
  [
   63
  ],
  104,
  "(((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y)))"
 ],
 [
  "DEL",
  [
   66
  ],
  105,
  "((((x)*((y)*(z)))+((x)*(y)))=((x)*(((y)*(z))+(y))))=>(((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y))))=>((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y)))))"
 ],
 [
  "DEL",
  [
   67
  ],
  106,
  "((((x)*(y))*(S(z)))=(((x)*((y)*(z)))+((x)*(y))))=>((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y))))"
 ],
 [
  "SV",
  [
   13,
   "y"
  ],
  107,
  "Ay0(((y)*(S(y0)))=(((y)*(y0))+(y)))"
 ],
 [
  "SV",
  [
   69,
   "z"
  ],
  108,
  "((y)*(S(z)))=(((y)*(z))+(y))"
 ],
 [
  "SV",
  [
   4,
   "(x)*((y)*(S(z)))"
  ],
  109,
  "((x)*((y)*(S(z))))=((x)*((y)*(S(z))))"
 ],
 [
  "SV",
  [
   5,
   "(y)*(S(z))"
  ],
  110,
  "Ay0((((y)*(S(z)))=(y0))=>((P[(y)*(S(z))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   72,
   "((y)*(z))+(y)"
  ],
  111,
  "(((y)*(S(z)))=(((y)*(z))+(y)))=>((P[(y)*(S(z))])=>(P[((y)*(z))+(y)]))"
 ],
 [
  "DEL",
  [
   72
  ],
  112,
  "Ay0((((y)*(S(z)))=(y0))=>((P[(y)*(S(z))])=>(P[y0])))"
 ],
 [
  "S",
  [
   73,
   "P",
   "((x)*((y)*(S(z))))=((x)*(@))"
  ],
  113,
  "(((y)*(S(z)))=(((y)*(z))+(y)))=>((((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y)))))"
 ],
 [
  "DEL",
  [
   73
  ],
  114,
  "(((y)*(S(z)))=(((y)*(z))+(y)))=>((P[(y)*(S(z))])=>(P[((y)*(z))+(y)]))"
 ],
 [
  "MP",
  [
   74,
   70
  ],
  115,
  "(((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y))))"
 ],
 [
  "MP",
  [
   75,
   71
  ],
  116,
  "((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y)))"
 ],
 [
  "DEL",
  [
   71
  ],
  117,
  "((x)*((y)*(S(z))))=((x)*((y)*(S(z))))"
 ],
 [
  "DEL",
  [
   74
  ],
  118,
  "(((y)*(S(z)))=(((y)*(z))+(y)))=>((((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y)))))"
 ],
 [
  "DEL",
  [
   75
  ],
  119,
  "(((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y))))"
 ],
 [
  "SV",
  [
   5,
   "(x)*((y)*(S(z)))"
  ],
  120,
  "Ay0((((x)*((y)*(S(z))))=(y0))=>((P[(x)*((y)*(S(z)))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   77,
   "(x)*(((y)*(z))+(y))"
  ],
  121,
  "(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y))))=>((P[(x)*((y)*(S(z)))])=>(P[(x)*(((y)*(z))+(y))]))"
 ],
 [
  "DEL",
  [
   77
  ],
  122,
  "Ay0((((x)*((y)*(S(z))))=(y0))=>((P[(x)*((y)*(S(z)))])=>(P[y0])))"
 ],
 [
  "S",
  [
   78,
   "P",
   "(@)=((x)*((y)*(S(z))))"
  ],
  123,
  "(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y))))=>((((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z))))))"
 ],
 [
  "DEL",
  [
   78
  ],
  124,
  "(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y))))=>((P[(x)*((y)*(S(z)))])=>(P[(x)*(((y)*(z))+(y))]))"
 ],
 [
  "SV",
  [
   4,
   "(x)*((y)*(S(z)))"
  ],
  125,
  "((x)*((y)*(S(z))))=((x)*((y)*(S(z))))"
 ],
 [
  "MP",
  [
   79,
   76
  ],
  126,
  "(((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z)))))"
 ],
 [
  "MP",
  [
   81,
   80
  ],
  127,
  "((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z))))"
 ],
 [
  "SV",
  [
   5,
   "(x)*(((y)*(z))+(y))"
  ],
  128,
  "Ay0((((x)*(((y)*(z))+(y)))=(y0))=>((P[(x)*(((y)*(z))+(y))])=>(P[y0])))"
 ],
 [
  "SV",
  [
   83,
   "(x)*((y)*(S(z)))"
  ],
  129,
  "(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z)))))=>((P[(x)*(((y)*(z))+(y))])=>(P[(x)*((y)*(S(z)))]))"
 ],
 [
  "DEL",
  [
   83
  ],
  130,
  "Ay0((((x)*(((y)*(z))+(y)))=(y0))=>((P[(x)*(((y)*(z))+(y))])=>(P[y0])))"
 ],
 [
  "S",
  [
   84,
   "P",
   "(((x)*(y))*(S(z)))=(@)"
  ],
  131,
  "(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z)))))=>(((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y))))=>((((x)*(y))*(S(z)))=((x)*((y)*(S(z))))))"
 ],
 [
  "DEL",
  [
   84
  ],
  132,
  "(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z)))))=>((P[(x)*(((y)*(z))+(y))])=>(P[(x)*((y)*(S(z)))]))"
 ],
 [
  "MP",
  [
   85,
   82
  ],
  133,
  "((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y))))=>((((x)*(y))*(S(z)))=((x)*((y)*(S(z)))))"
 ],
 [
  "MP",
  [
   86,
   68
  ],
  134,
  "(((x)*(y))*(S(z)))=((x)*((y)*(S(z))))"
 ],
 [
  "DEL",
  [
   79
  ],
  135,
  "(((x)*((y)*(S(z))))=((x)*(((y)*(z))+(y))))=>((((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z))))))"
 ],
 [
  "DEL",
  [
   80
  ],
  136,
  "((x)*((y)*(S(z))))=((x)*((y)*(S(z))))"
 ],
 [
  "DEL",
  [
   81
  ],
  137,
  "(((x)*((y)*(S(z))))=((x)*((y)*(S(z)))))=>(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z)))))"
 ],
 [
  "DEL",
  [
   82
  ],
  138,
  "((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z))))"
 ],
 [
  "DEL",
  [
   85
  ],
  139,
  "(((x)*(((y)*(z))+(y)))=((x)*((y)*(S(z)))))=>(((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y))))=>((((x)*(y))*(S(z)))=((x)*((y)*(S(z))))))"
 ],
 [
  "DEL",
  [
   86
  ],
  140,
  "((((x)*(y))*(S(z)))=((x)*(((y)*(z))+(y))))=>((((x)*(y))*(S(z)))=((x)*((y)*(S(z)))))"
 ],
 [
  "DT",
  [
   41,
   87
  ],
  141,
  "((((x)*(y))*(z))=((x)*((y)*(z))))=>((((x)*(y))*(S(z)))=((x)*((y)*(S(z)))))"
 ],
 [
  "G",
  [
   88,
   "x"
  ],
  142,
  "Ax(((((x)*(y))*(z))=((x)*((y)*(z))))=>((((x)*(y))*(S(z)))=((x)*((y)*(S(z))))))"
 ],
 [
  "SV",
  [
   89,
   "t"
  ],
  143,
  "((((t)*(y))*(z))=((t)*((y)*(z))))=>((((t)*(y))*(S(z)))=((t)*((y)*(S(z)))))"
 ],
 [
  "G",
  [
   90,
   "z"
  ],
  144,
  "Az(((((t)*(y))*(z))=((t)*((y)*(z))))=>((((t)*(y))*(S(z)))=((t)*((y)*(S(z))))))"
 ],
 [
  "SV",
  [
   91,
   "x"
  ],
  145,
  "((((t)*(y))*(x))=((t)*((y)*(x))))=>((((t)*(y))*(S(x)))=((t)*((y)*(S(x)))))"
 ],
 [
  "G",
  [
   92,
   "x"
  ],
  146,
  "Ax(((((t)*(y))*(x))=((t)*((y)*(x))))=>((((t)*(y))*(S(x)))=((t)*((y)*(S(x))))))"
 ],
 [
  "G",
  [
   40,
   "x"
  ],
  147,
  "Ax((((x)*(y))*(0))=((x)*((y)*(0))))"
 ],
 [
  "SV",
  [
   94,
   "t"
  ],
  148,
  "(((t)*(y))*(0))=((t)*((y)*(0)))"
 ],
 [
  "S",
  [
   14,
   "P",
   "(((t)*(y))*(@))=((t)*((y)*(@)))"
  ],
  149,
  "((((t)*(y))*(0))=((t)*((y)*(0))))=>((Ax(((((t)*(y))*(x))=((t)*((y)*(x))))=>((((t)*(y))*(S(x)))=((t)*((y)*(S(x)))))))=>(Ax((((t)*(y))*(x))=((t)*((y)*(x))))))"
 ],
 [
  "MP",
  [
   96,
   95
  ],
  150,
  "(Ax(((((t)*(y))*(x))=((t)*((y)*(x))))=>((((t)*(y))*(S(x)))=((t)*((y)*(S(x)))))))=>(Ax((((t)*(y))*(x))=((t)*((y)*(x)))))"
 ],
 [
  "MP",
  [
   97,
   93
  ],
  151,
  "Ax((((t)*(y))*(x))=((t)*((y)*(x))))"
 ],
 [
  "SV",
  [
   98,
   "z"
  ],
  152,
  "(((t)*(y))*(z))=((t)*((y)*(z)))"
 ],
 [
  "G",
  [
   99,
   "z"
  ],
  153,
  "Az((((t)*(y))*(z))=((t)*((y)*(z))))"
 ],
 [
  "G",
  [
   100,
   "y"
  ],
  154,
  "Ay(Az((((t)*(y))*(z))=((t)*((y)*(z)))))"
 ],
 [
  "G",
  [
   101,
   "t"
  ],
  155,
  "At(Ay(Az((((t)*(y))*(z))=((t)*((y)*(z))))))"
 ],
 [
  "SV",
  [
   102,
   "x"
  ],
  156,
  "Ay(Az((((x)*(y))*(z))=((x)*((y)*(z)))))"
 ],
 [
  "G",
  [
   103,
   "x"
  ],
  157,
  "Ax(Ay(Az((((x)*(y))*(z))=((x)*((y)*(z))))))"
 ]
];