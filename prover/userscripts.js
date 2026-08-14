'use strict';
function alreadyProved(sentence) {
    for (const [i,s] of globalProver.statements.entries()) {
        if (s.p.sentence === sentence) return true;
    }
    return false;
}
var userWants = new Map();
function doTransforms(arr, DEL=true) {
    console.log('doTransforms:', arr);
    var currentStatement = arr[0];
    for (var i = 1; i < arr.length; ++ i) { 
        if (currentStatement == 0) {updatePage(); throw new Error("Failed in doTransforms");}
        if (arr[i] == 'SV') {
            var variable = arr[i+1];
            if (variable == 'new') variable = 't85383';
            var temp = globalProver.SV(currentStatement, variable);
            if (DEL&&i > 1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 1;
        } else if (arr[i] == 'GE') {
            var sentence = arr[i+1];
            var temp = globalProver.GE(currentStatement, sentence);
            if (DEL&&i > 1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 1;
        } else if (arr[i] == 'G') {
            var variable = arr[i+1];
            if (variable == 'new') variable = 't85383';
            var temp = globalProver.G(currentStatement, variable);
            if (DEL&&i > 1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 1;
        } else if (arr[i] == 'S') {
            var gen = arr[i+1], target = arr[i+2];
            var temp = globalProver.S(currentStatement, gen, target);
            if (DEL&&i > 1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 2;
        } else if (arr[i] == 'Rewrite') {
            const claim = arr[i+1];
            var temp = globalProver.Rewrite(currentStatement, claim);
            if (DEL&&i > 1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 1;
        } else if (arr[i] == 'DT') {
            const other = arr[i+1];
            var temp = globalProver.DT(other, currentStatement);
            if (DEL && i>1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 1;
        } else if (arr[i] == 'SubRelation') {
            const others = arr.slice(i+1, i+1+2);
            var temp = globalProver.SubRelation(currentStatement, ...others);
            if (DEL && i>1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 2;
        } else if (arr[i] == 'SubFunction') {
            const others = arr.slice(i+1, i+1+2);
            var temp = globalProver.SubFunction(currentStatement, ...others);
            if (DEL && i>1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 2;
        } else if (arr[i] == 'MP') {
            const next = arr[i+1];
            const s1 = globalProver.statements.get(currentStatement).p.sentence;
            const s2 = globalProver.statements.get(next).p.sentence;
            let longer = currentStatement, shorter = next;
            if (s1.length < s2.length) {
                longer = next;
                shorter = currentStatement;
            }
            var temp = globalProver.MP(longer, shorter);
            if (DEL && i > 1) deleteStatement(currentStatement);
            currentStatement = temp;
            i += 1;
        } else throw new Error('asdfasdfasdfassad ' + arr[i]);
        if (currentStatement == 0) {
            updatePage();
            throw new Error("prover step failed: " + globalProver.currentError + ' ' + arr[i]);
        }
    }
    return currentStatement;
}
function removeDefDep(new_id, defVar, defId, defStParent) {
    const fixedProver = globalProver;
    if (!globalProver.statements.has(new_id)) return;
    if (!globalProver.statements.has(defId)) return;
    const statement = globalProver.statements.get(new_id);
    const deps = statement.deps;
    const p = statement.p;
    // if defId is the id of an assumption of this statement
    // AND it's the only assumption that mentions #x
    // AND this new statement doesn't mention #x
    // then can do it
    if (!deps.includes(defId)) return '';
    if (p.free.includes(defVar)) return '';
    let included = false;
    for (const depId of deps) {
        if (depId == defId) continue;
        const depSt = fixedProver.statements.get(depId);
        if (depSt.p.free.includes(defVar)) {
            included = true;
        }
    }
    if (included) return '';
    console.log('GOT ONE!!!', defVar, p.sentence, defId, new_id);
    const s1 = fixedProver.DT(defId, new_id);
    const s2 = fixedProver.G(s1, defVar);
    const defSt = fixedProver.statements.get(defId)
    const defStParentSafe = defStParent || defSt.used[0];
    const t11 = fixedProver.S(7, 'Q', 'Q123');
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    const t12 = fixedProver.S(t11, 'P', 'P123[@]');
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    const t1 = fixedProver.S(t12, 'Q123', p.sentence);
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    const t2 = fixedProver.S(t1, 'P123', renameDisallowed(parseSentence(replaceVariable(defSt.p.sentence, defVar, '@')), p.free)[0].sentence);
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    const t3 = fixedProver.MP(t2, defStParentSafe);
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    const t4 = fixedProver.MP(t3, s2);
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    const t5 = fixedProver.Rewrite(t4, p.sentence);
    if (fixedProver.currentError) console.log(fixedProver.currentError);
    console.log(s1, s2, defSt, t1, t2, t3, t4, t5);
    if (t5 == 0) {
    updatePage();
    console.log(fixedProver.statements.get(s1).p.sentence);
    console.log(fixedProver.statements.get(s2).p.sentence);
    console.log(fixedProver.statements.get(t1).p.sentence);
    console.log(fixedProver.statements.get(t2).p.sentence);
    console.log(fixedProver.statements.get(defStParentSafe).p.sentence);
    console.log(fixedProver.statements.get(t3).p.sentence);
    console.log(fixedProver.statements.get(t4).p.sentence);
    }
    else {
        for (const del_id of [s1, s2, t11, t12, t1, t2, t3, t4])
            fixedProver.DEL(del_id);
    }
    return t5;
}
function isAdditionTerm(tp) {
    if (tp[0] == '+') {
        const a1 = isAdditionTerm(tp[1].parsed), a2 = isAdditionTerm(tp[2].parsed);
        if (a1[0]==false || a2[0]==false) return [false];
        return [true, a1[1].concat(a2[1])];
    } else if (tp[0] == 'S') {
        const a1 = isAdditionTerm(tp[1].parsed);;
        if (a1[0]==false) return [false];
        return [true, ['S'].concat(a1[1])];
    } else if (tp[0][0] == '#' || (tp[0][0] >= 'a' && tp[0][0] <= 'z')) {
        return [true, [tp[0]]];
    } else if (tp[0] == '0') {
        return [true, []];
    } else return [false];
}
var currentTermSentence;
var currentTermIdx;
function termToRewrite(t) {
    document.getElementById('userTerm').innerHTML = t;
    currentTerm = t;
}
function userInputUpdated() {
    const s = document.getElementById('assumptionInput').value;
    if (s.startsWith('!')) return;
    const p = parseSentence(s);
    document.getElementById('errorLogging').innerHTML = renderParsed(p) + ' ' + (p.error||'');
}
function swapEqual(i) {
    if (i == 0) throw new Error("statement is 0");
    const s = globalProver.statements.get(i);
    const sp = s.p.parsed;
    const u = sp[2][0].sentence, v = sp[2][1].sentence;
    if (u == v) return;
    var temp = doTransforms([5, 'S', 'P', 'P123', 'SV', u, 'SV', v, 'S', 'P123', `(@)=(${u})`]);
    var temp2 = globalProver.SV(4, u); // u=u
    var temp3 = globalProver.MP(temp, i);
    var temp4 = globalProver.MP(temp3, temp2);
    deleteStatement(temp);
    deleteStatement(temp2);
    deleteStatement(temp3);
    return temp4;
}
function splitAnd(id) {
    const s = globalProver.statements.get(id);
    const P = s.p.parsed;
    if (!globalProver.filesImported.includes('logic')) {
        alert('cannot magic the AND, since logic not imported');
        return '';
    }
    var s1 = P[2][0].sentence, s2 = P[2][1].sentence;
    var ae1 = globalProver.Quote('and_elimination1');
    var ae2 = globalProver.Quote('and_elimination2');
    var temp1 = doTransforms([ae1, 'S', 'P', 'P123', 'S', 'Q', 'Q123', 'S', 'P123', s1, 'S', 'Q123', s2]);
    var temp2 = doTransforms([ae2, 'S', 'P', 'P123', 'S', 'Q', 'Q123', 'S', 'P123', s1, 'S', 'Q123', s2]);
    var final1 = globalProver.MP(temp1, id);
    var final2 = globalProver.MP(temp2, id);
    for (var k of [ae1, ae2, temp1, temp2]) deleteStatement(k);
    return [final1, final2];
}
function convertFun(name, arity, predArity, defn) {
    console.log('CONVERTFUN', name, arity, predArity, defn);
    const sentence = "('Eval[" + defn + ';])=(@' + (arity+1) + ')';
    const sentenceForFun = "('Eval[" + defn + ';])=(@)';
    console.log(sentence);
    const parsed = parseSentence(sentence, true);
    if (parsed.error !== undefined) { alert(parsed.error); return ''; }
    console.log("parsedOk");
    const [existence, uniqueness] = proveFunction(parsed, predArity);
    if (existence === undefined) return '';
    console.log("proveFunction ok");
    globalProver.AddFunction(arity, name, sentenceForFun, existence, uniqueness, predArity);
    //deleteStatement(existence);
    //deleteStatement(uniqueness);
    // want to prove: const[blah] => blah[Blah]
    // and const[blah] => (Ax blah[x] => x=Blah)
    const disallowedVars = parsed.bound;
    const disallowedNumbers = disallowedVars.flatMap(v => v.length > 1 ? [+v.slice(1)] : []);
    const bigNumber = Math.max(...[0].concat(disallowedNumbers)) + 1;
    const atVariable = 'x'+bigNumber;
    const strictDefn = defn.replaceAll('@', atVariable);
    const strictFunctionCall = name + "[" + arange(predArity).map(i => "P"+(i+1)).join(",") + ";" + arange(arity).map(i => atVariable+(i+1)).join(",") + "]";
    console.log(strictFunctionCall);
    const cass = globalProver.Assume("'const[" + strictDefn + ";]");
    const evalExists = globalProver.Quote("Eval exists")
    const blah = doTransforms([4, "SV", "'Eval[" + strictDefn + ";]", "Rewrite", "(" + strictFunctionCall + ")=('Eval["+strictDefn+";])"]);
    const swappedBlah = swapEqual(blah);
    const x = doTransforms([evalExists, "S", "P", strictDefn,
            //...arange(arity).flatMap(idx => ['G', atVariable + (arity-idx)])
            ]
            );
    const y = doTransforms([5, "S", "P", strictDefn.slice(0,-1) + ",@]", "SV", "'Eval["+strictDefn+";]", "SV", strictFunctionCall, "MP", swappedBlah]);
    const innerFinal = doTransforms([cass, "MP", x, "MP", y]);
    const final1 = doTransforms([innerFinal, "DT", cass, ...arange(arity).flatMap(idx => ['G', atVariable + (arity-idx)])])
    const existUnique = globalProver.SubRelation(cass, "'const", 0);
    const otherAss = globalProver.Assume(strictDefn.slice(0,-1) + "," + atVariable + "]");
    const ae2 = globalProver.Quote("and_elimination2");
    const [andleft, andright] = globalProver.statements.get(existUnique).p.parsed[2];
    const uniqueOnly = doTransforms([ae2, "S", "P", "P123", "S", "Q", "Q123", "S", "P123", andleft.sentence, "S", "Q123", andright.sentence, "MP", existUnique,
        "SV", atVariable, "SV", strictFunctionCall, "MP", otherAss, "MP", innerFinal,
        "DT", otherAss, "G", atVariable, "DT", cass,
            ...arange(arity).flatMap(idx => ['G', atVariable + (arity-idx)])
        ]);
    for (const d of [cass, evalExists, blah, swappedBlah, x, y, ae2, existence, uniqueness, otherAss, innerFinal]) deleteStatement(d);
    return [final1, uniqueOnly];
}
function proveFunction(parsed, predArity) { // ...@1 @2... =@3
    console.log(parsed, predArity);
    if (parsed.parsed[0] !== '=') return '';
    console.log('EQUALS');
    const rhs = parsed.parsed[2][1].sentence;
    if (rhs[0] !== '@') return '';
    console.log('RHS@');
    const arity = +rhs.slice(1);
    const allowedFree = arange(arity-1).map(i => '@'+(i+1));
    for (const myfree of parsed.parsed[2][0].free) if (!allowedFree.includes(myfree)) return '';
    console.log('LHS FREE');
    const allowedGens = arange(predArity).map(i => 'P' + (i+1));
    for (const mygen of parsed.generics) if (!allowedGens.includes(mygen)) return '';
    console.log('GENS');
    const disallowedVars = parsed.bound;
    const disallowedNumbers = disallowedVars.flatMap(v => v.length > 1 ? [+v.slice(1)] : []);
    const bigNumber = Math.max(...[0].concat(disallowedNumbers)) + 1;
    const expr = parsed.parsed[2][0].sentence.replaceAll('@', 'z'+bigNumber);
    const termArgs = arange(arity-1).map(idx => ('z'+bigNumber)+(idx+1)).join(',');
    const existence = doTransforms([
        4,
        'SV', expr,
        'GE', 'Ey' + bigNumber + '((' + expr + ')=(y'+bigNumber+'))',
        ...arange(arity-1).flatMap(idx => ['G', ('z'+bigNumber) + (arity-1-idx)]),
        ]);
    const ass0 = globalProver.Assume('(' + expr + ')=(y' + bigNumber + ')');
    const ass1 = globalProver.Assume('(' + expr + ')=(y' + (bigNumber+1) + ')');
    const uniqueness = doTransforms([5, 'S', 'P', '(@)=(y'+(bigNumber+1)+')', 'SV', expr, 'SV', 'y'+bigNumber,
        'G', 'y'+(bigNumber+1), 'G', 'y'+bigNumber,
        ...arange(arity-1).flatMap(idx => ['G', ('z'+bigNumber) + (arity-1-idx)]),
        ]);
    for (var k of [ass0, ass1])
        deleteStatement(k);
    return [existence, uniqueness];
}
window.userModifyInput = function(s) {
    if (s[0] !== '!') return s;
    if (s.startsWith('! ') && /^[0-9]+ and [0-9]+$/.test(s.slice(2))) {
        const [id1, id2] = s.slice(2).split(' and ').map(x => +x);
        const s1 = globalProver.statements.get(id1), s2 = globalProver.statements.get(id2);
        if ((!(s1))||(!(s2))) return '';
        if (!globalProver.filesImported.includes('logic')) {
            alert('cannot magic introduce AND, since logic not imported');
            return '';
        }
        var ai = globalProver.Quote('and_introduction');
        const a = s1.p.sentence, b = s2.p.sentence;
        console.log(a,b);
        var temp1 = doTransforms([
            ai,
            'S', 'P', a, 'S', 'Q', b,
            ]);
        var temp2 = globalProver.MP(temp1, id1);
        var temp3 = globalProver.MP(temp2, id2);
        deleteStatement(ai);
        deleteStatement(temp1);
        deleteStatement(temp2);
    }
    if (s.startsWith('!rewrite ')) {
        termToRewrite(s.slice(8));
        return '';
    }
    if (s.startsWith("!convertFun ")) { // e.g. !convertFun 'Size 0 1 'size[P1;]              -> Eval['size]
        let [_, name, arity, predArity, defn] = s.split(' ');
        arity = +arity;
        predArity = +predArity;
        convertFun(name, arity, predArity, defn);
        updatePage();
        return '';
    }
    if (s.startsWith('!newRecur ')) {
        // define a function which is inductive in its last argument (so arity >= 1)
        let [_, name, arity, predArity, defn0, defnind] = s.split(' ');
        console.log(defn0, defnind);
        arity = +arity;
        predArity = +predArity;
        const defn0strict = defn0.replaceAll("@", "x");
        const nameInd = name.toLowerCase() + "auxind"; // relation defining the inductive function
        const nameIndCurried = nameInd + "[" + arange(predArity).map(i => "P"+(i+1)).join(",") + ";" + arange(arity-1).map(i => "@"+(i+1)).join(",") + "]"; // above curried to only have 2 term args
        const nameIndCurriedStrict = nameIndCurried.replaceAll("@", "x");
        const nameCurried = name + "[" + arange(predArity).map(i => "P"+(i+1)).join(",") + ";" + arange(arity-1).map(i => "@"+(i+1)).join(",") + "]";
        const nameCurriedStrict = nameCurried.replaceAll("@", "x");
        console.log(nameInd, defnind, nameIndCurried);
        globalProver.AddRelation(arity+2, nameInd, defnind, predArity);
        const [recurOfNew, recurImpliesNew] = convertFun(name, arity, predArity, "'recur[" + nameIndCurried + ";" + defn0 + ",@" + arity + "]");
        console.log(recurOfNew, recurImpliesNew);
        const cass = globalProver.Assume("'const2[" + nameIndCurriedStrict + ";]");
        const [q1, q2, q3] = ["recur const2", "recursion base definition", "const2 recursion nonzero reverse"].map(q => globalProver.Quote(q));
        const f2r = doTransforms([q1, "S", "P", nameIndCurriedStrict, "MP", cass, "SubRelation", "'const2", 0, "SV", defn0strict, "SV", "y"]);
        const a = doTransforms([recurImpliesNew, ...arange(arity-1).flatMap(i => ["SV", "x"+(i+1)]), "SV", "y", "MP", f2r, "G", "y"], false);
        const aa = doTransforms([recurOfNew, ...arange(arity-1).flatMap(i => ["SV", "x"+(i+1)]), "SV", "y", "MP", f2r, "G", "y"]);
        const b = doTransforms([a, "SV", "0", "SV", defn0strict]);
        let c = doTransforms([q2, "S", "P", nameIndCurriedStrict, "SV", defn0strict, "MP", b]);
        let c1 = 0, c2 = 0;
        const fn = doTransforms([aa, "SV", "n"]);
        const fSn = doTransforms([aa, "SV", "S(n)"]);
        let d1 = doTransforms([q3, "S", "P", nameIndCurriedStrict, "MP", cass, "SV", defn0strict, "SV", "n", "SV", nameCurriedStrict.slice(0,-1) + ",n]", "SV", nameCurriedStrict.slice(0,-1) + ",S(n)]",
            "MP", fn, "MP", fSn, "SubRelation", nameInd, 0]);
        let d2 = 0, d3 = 0;
        console.log(globalProver.statements.get(c).p.sentence, c);
        if (globalProver.statements.get(c).p.parsed[0] == "=") {
            c1 = swapEqual(c);
            c2 = doTransforms([c1, "DT", cass]);
        } else {
            c2 = doTransforms([c, "DT", cass]);
        }
        if (globalProver.statements.get(d1).p.parsed[0] == "=") {
            d2 = swapEqual(d1);
            d3 = doTransforms([d2, "G", "n", "DT", cass]);
        } else {
            d3 = doTransforms([d1, "G", "n", "DT", cass]);
        }
        for (const d of [a, aa, b, fn, fSn, f2r, cass, recurOfNew, recurImpliesNew, q1, q2, q3, c, c1, d2, d1]) if (d) deleteStatement(d);
        updatePage();
        return '';
    }
    if (s.startsWith('!proveFun ')) {
        if (!globalProver.filesImported.includes('logic')) {
            alert('cannot magic the AND, since logic not imported');
            return '';
        }
        const args = s.split(' ');
        if (args.length > 2) { // NewExpression 3 0 (((@1)+(@2))*(@3))=(@4)
            const [_, name, arity, predArity, defn] = args;
            const parsedArgument = parseSentence(defn, true);
            const [ex, un] = proveFunction(parsedArgument, +predArity);
            if (ex === undefined) return '';
            globalProver.AddFunction(+arity, name, defn.slice(0,-2)+')', ex, un, +predArity);
            const functionCall = name + "[" + arange(+predArity).map(i => "P" + (i+1)).join(',') + ';' + arange(+arity).map(i => "x" + (i+1)).join(',') + ']';
            const andAss = doTransforms([4, "SV", functionCall, "SubFunction", name, 1, "SV", "#z"]);
            const [a1, a2] = splitAnd(andAss);
            const funcExpr = globalProver.statements.get(a1).p.parsed[2][0].sentence;
            console.log(funcExpr);
            const firstEq = doTransforms([4, "SV", funcExpr]);
            const intermediateEq = doTransforms([5, "S", "P", "(@)=("+funcExpr+")", "SV", funcExpr, "SV", "#z", "MP", a1, "MP", firstEq]);
            const finalEq = doTransforms([5, "S", "P", "(@)=("+funcExpr+")", "SV", "#z", "SV", functionCall, "MP", a2, "MP", intermediateEq]);
            const ungenResult = removeDefDep(finalEq, "#z", andAss);
            const result = doTransforms([ungenResult, ...arange(+arity).flatMap(i => ["G", "x"+(arity-i)])]);
            for (const d of [ex, un, andAss, intermediateEq, firstEq, finalEq, ungenResult]) deleteStatement(d);
            return '';
        }
        const argument = args[1];
        if (!globalProver.orcMap.has(argument)) return '';
        console.log("has symbol");
        const symbol = argument;
        const [typename, arity, defn, predArity] = globalProver.orcMap.get(symbol);
        const parsed = parseSentence(defn, true);
        if (parsed.parsed[0] === '=') { // function like x+2*y=z
            console.log(parsed, arity);
            if (parsed.parsed[2][1].sentence != '@'+arity) return '';
            if (parsed.parsed[2][0].free.includes('@'+arity)) return '';
            const disallowedVars = parsed.bound;
            const disallowedNumbers = disallowedVars.flatMap(v => v.length > 1 ? [+v.slice(1)] : []);
            const bigNumber = Math.max(...[0].concat(disallowedNumbers)) + 1;
            const expr = parsed.parsed[2][0].sentence.replaceAll('@', 'z'+bigNumber);
            const termArgs = arange(arity-1).map(idx => ('z'+bigNumber)+(idx+1)).join(',');
            const predArgs = arange(predArity).map(idx => ('P')+(idx+1)).join(',');
            const existence = doTransforms([
                4,
                'SV', expr,
                'Rewrite', symbol + "[" + predArgs + ';' + termArgs + ','+expr+']',
                'GE', 'Ey' + bigNumber + '(' + symbol + "[" + predArgs + ';' + termArgs + ','+'y'+bigNumber+'])',
    //            'GE', 'Ey'+bigNumber+'(('+expr+')=(y'+bigNumber+'))',
                ]);
            const ass0 = globalProver.Assume(symbol + "[" + predArgs + ';' + termArgs + ','+'y'+bigNumber+']');
            const ass1 = globalProver.Assume(symbol + "[" + predArgs + ';' + termArgs + ','+'y'+(bigNumber+1)+']');
            console.log("logging", ass0, symbol);
            const y0 = globalProver.SubRelation(ass0, symbol, 0);
            const y1 = globalProver.SubRelation(ass1, symbol, 0);
            const uniqueness = doTransforms([5, 'SV', expr, 'SV', 'y'+bigNumber, 'S', 'P', '(@)=(y'+(bigNumber+1)+')',
                'MP', y0, 'MP', y1,
                'DT', ass1, 'DT', ass0,
                'G', 'y'+(bigNumber+1), 'G', 'y'+bigNumber,
                ]);
            const ai = globalProver.Quote('and_introduction');
            const symbolWithPredArgs = predArity > 0 ? symbol + '[' + predArgs + ';]' : symbol;
            const myfunc = doTransforms([ai, 'S', 'P', 'P123', 'S', 'Q', 'Q123',
                'S', 'P123', globalProver.statements.get(existence).p.sentence,
                'S', 'Q123', globalProver.statements.get(uniqueness).p.sentence,
                'MP', existence, 'MP', uniqueness,
                'Rewrite', "'const" + "[" + symbol + "[" + predArgs + ';' + termArgs + "];]",
                ...arange(arity-1).flatMap(idx => ['G', ('z'+bigNumber) + (arity-1-idx)]),
                'Rewrite', "'const" + (arity == 1 ? '' : ''+(arity-1)) + "[" + symbolWithPredArgs + ";]"
            ]);

            for (var k of [existence, ass0, ass1, y0, y1, uniqueness, ai])
                deleteStatement(k);

        } else if (globalProver.orcMap.has(parsed.parsed[0])) { // function like 'foo['bar;x*x,y+0,z]
            console.log(typename, arity, predArity, defn);
            const bigNumber = Math.floor(Math.random()*100000); // TODO fix
            const newAt = 'z'+bigNumber;
            const newdefn = defn.replaceAll('@', newAt);
            const newparsed = parseSentence(newdefn);
            const innerSymbol = newparsed.parsed[0];
            const parsedPreds = newparsed.parsed[1]; // TODO fix
            const innernpreds = parsedPreds.length;
            const parsedTerms = newparsed.parsed[2];
            const symbolPreds = arange(predArity).map(i=>"P"+(i+1)).join(",")+";";
            const [_, innerArity, innerDefn, innerPredArity] = globalProver.orcMap.get(innerSymbol);
            const innernargs = innerArity-1;
            const target = newAt + arity;
            const nargs = arity-1;
            const innerfuncSymbol = innernargs == 1 ? "'func" : "'func"+innernargs;
            const funcSymbol = nargs == 1 ? "'func" : "'func"+nargs;
            console.log(parsedPreds, parsedTerms.slice(0,-1), target, nargs);
            if (parsedTerms[parsedTerms.length-1].sentence !== target) return '';
            for (const pred of parsedPreds) if (pred.free.includes(target)) return '';
            for (const term of parsedTerms.slice(0,-1)) if (term.free.includes(target)) return '';
            const assSentence = innerfuncSymbol+"["+innerSymbol+"["+parsedPreds.map(p=>p.sentence).join(",")+";];]";
            console.log("assumption:", assSentence);
            const assumption = globalProver.Assume(assSentence);
            const expanded = globalProver.SubRelation(assumption, innerfuncSymbol, 0);

            const P = globalProver.statements.get(expanded).p.parsed;
            const s1 = P[2][0].sentence, s2 = P[2][1].sentence;
            const ae1 = globalProver.Quote('and_elimination1');
            const ae2 = globalProver.Quote('and_elimination2');
            const temp1 = doTransforms([ae1, 'S', 'P', 'P123', 'S', 'Q', 'Q123', 'S', 'P123', s1, 'S', 'Q123', s2]);
            const temp2 = doTransforms([ae2, 'S', 'P', 'P123', 'S', 'Q', 'Q123', 'S', 'P123', s1, 'S', 'Q123', s2]);
            const baselineExists = globalProver.MP(temp1, expanded);
            const baselineUnique = globalProver.MP(temp2, expanded);
            for (const k of [expanded, ae1, ae2, temp1, temp2]) deleteStatement(k);

            const transformedExistsInner = doTransforms(
                [baselineExists]
                .concat(arange(innernargs).flatMap(i=>['SV', parsedTerms[i].sentence]))
                .concat([
                    "SV", "#a"+bigNumber, "Rewrite", symbol+"["+symbolPreds + arange(nargs).map(i=>newAt+(i+1)).join(",")+","+"#a"+bigNumber+"]",
                    "GE", "Ey("+ symbol+"["+symbolPreds + arange(nargs).map(i=>newAt+(i+1)).join(",")+","+"y]" + ")",
                ])
            );
            const depRemoved = removeDefDep(transformedExistsInner, "#a"+bigNumber, baselineExists +1+ innernargs+1);
            const transformedExists = doTransforms(
                [depRemoved]
                .concat(arange(nargs).flatMap(i=>['G', newAt + (nargs-i)]))
            );
            for (const k of [baselineExists, depRemoved, transformedExistsInner]) deleteStatement(k);

            const ua1 = globalProver.Assume(symbol+"["+symbolPreds+arange(nargs).flatMap(i=>newAt+(i+1)).join(",")+",y1]");
            const ua2 = globalProver.Assume(symbol+"["+symbolPreds+arange(nargs).flatMap(i=>newAt+(i+1)).join(",")+",y2]");
            const ua1Expanded = globalProver.SubRelation(ua1, symbol, 0);
            const ua2Expanded = globalProver.SubRelation(ua2, symbol, 0);
            const transformedUnique = doTransforms(
                [baselineUnique]
                .concat(arange(innernargs).flatMap(i=>["SV", parsedTerms[i].sentence]))
                .concat(["SV", "y1", "SV", "y2", "MP", ua1Expanded, "MP", ua2Expanded, "DT", ua2, "DT", ua1, "G", "y2", "G", "y1"])
                .concat(arange(nargs).flatMap(i=>["G", newAt+(nargs-i)]))
            )
            for (const k of [ua1, ua2, ua1Expanded, ua2Expanded, baselineUnique]) deleteStatement(k);
            const ai = globalProver.Quote('and_introduction');
            const x1 = doTransforms([ai, 'S', 'P', 'P123', 'S', 'Q', 'Q123',
                'S', 'P123', globalProver.statements.get(transformedExists).p.sentence,
                'S', 'Q123', globalProver.statements.get(transformedUnique).p.sentence,
                'MP', transformedExists, 'MP', transformedUnique]);
            const isFunc = doTransforms([x1, "Rewrite", funcSymbol+"["+symbol+"["+symbolPreds+"];]", "DT", assumption]);
            for (const k of [ai, transformedExists, transformedUnique, x1, assumption]) deleteStatement(k);
        }

        updatePage();
        return '';
    }
    if (s.startsWith('!def ')) {
        const inputs = s.split(' ');
        const new_id = +inputs[1];
        const defVar = inputs[2];
        const defId = +inputs[3];
        const defStParent = +inputs[4];
        const result = removeDefDep(new_id, defVar, defId, defStParent);
        updatePage();
        return '';
    }
    if (s.startsWith('!== ')) {
        const i = +s.split(' ')[1];
        const st = globalProver.statements.get(i);
        if (st.p.parsed[0] != '=') return;
//        if (s.deleted || !s.highlight) continue;
        swapEqual(i);
        updatePage();
        return '';
    }
    if (s.startsWith('!= ')) {
        let [_, i, j] = s.split(' ');
        i = +i;
        j = +j;
        const st1 = globalProver.statements.get(i);
        const st2 = globalProver.statements.get(j);
        var sp = st1.p.parsed, tp = st2.p.parsed;
        if (sp[0] != '=' || tp[0] != '=') return;
        console.log(sp, tp);
        // st1: V1=V2, st2: V2=V3
        if (sp[2][1].sentence == tp[2][0].sentence) {
            var u = sp[2][0].sentence, v = sp[2][1].sentence, w = tp[2][1].sentence;
            if (u == w) return;
            //if (alreadyProved(`(${u})=(${w})`)) return;
            var temp6 = doTransforms([5, 'S', 'P', `(${u})=(@)`, 'SV', v, 'SV', w]);
            var temp3 = globalProver.MP(temp6, j);
            var temp4 = globalProver.MP(temp3, i);
            deleteStatement(temp3);
            deleteStatement(temp6);
        } else if (sp[2][0].sentence == tp[2][0].sentence) {
            var u = sp[2][0].sentence, v = sp[2][1].sentence, w = tp[2][1].sentence;
            if (v == w) return;
            //if (alreadyProved(`(${v})=(${w})`)) return;
            var i5 = doTransforms([5, 'S', 'P', `(@)=(${w})`, 'SV', u, 'SV', v]);
            var i6 = globalProver.MP(i5, i);
            var i7 = globalProver.MP(i6, j);
            for (var k of [i5, i6])
                deleteStatement(k);
        } else if (sp[2][1].sentence == tp[2][1].sentence) {
            var u = sp[2][0].sentence, v = sp[2][1].sentence, w = tp[2][0].sentence;
            if (u == w) return;
            //if (alreadyProved(`(${u})=(${w})`)) return;
            var b1 = doTransforms([5, 'S', 'P', `(@)=(${w})`, 'SV', w, 'SV', v]);
            var temp1 = globalProver.SV(4, w); // w=w
            var temp4 = globalProver.MP(b1, j); // w=w => v=w
            var temp5 = globalProver.MP(temp4, temp1); // v=w
            var b2 = doTransforms([5, 'S', 'P', `(${u})=(@)`, 'SV', v, 'SV', w]);
            var temp9 = globalProver.MP(b2, temp5);
            var temp10 = globalProver.MP(temp9, i); // u=w
            for (var k of [b1, temp1, temp4, temp5, b2, temp9])
                deleteStatement(k);
        }
        updatePage();
        return '';
    }
    if (s === '!t') { // import theorem
        const theoremName = prompt('What theorem? You know ' + [...globalProver.knownTheorems.keys()]);
        if (!theoremName) return '';
        if (!globalProver.knownTheorems.has(theoremName)) {
            let possibles = [];
            for (const [name, st] of globalProver.knownTheorems.entries()) {
                if (name.indexOf(theoremName) != -1) possibles.push(name);
            }
            alert(possibles);
            return;
        }
        globalProver.Quote(theoremName);
        updatePage();
        return '';
    }
    if (s.startsWith('!and ')) {
        if (!globalProver.filesImported.includes('logic')) {
            alert('cannot magic the AND, since logic not imported');
            return '';
        }
        const myArgs = s.split(' ');
        const ai = globalProver.Quote('and_introduction');
        const x1 = doTransforms([ai, 'S', 'P', 'P123', 'S', 'Q', 'Q123',
            'S', 'P123', globalProver.statements.get(+myArgs[1]).p.sentence,
            'S', 'Q123', globalProver.statements.get(+myArgs[2]).p.sentence,
            'MP', +myArgs[1], 'MP', +myArgs[2]]);
        for (const k of [ai]) deleteStatement(k);
        updatePage();
        return '';
    }
    if (s.startsWith('!addfunction ')) { // add function definition
        const myArgs = s.split(' ');
        globalProver.AddFunction(+myArgs[1], myArgs[2], myArgs[3], +myArgs[4], +myArgs[5], +myArgs[6]);
        updatePage();
        return '';
    }
    if (s.startsWith('!addfunc ')) { // no idea lol
        if (!globalProver.filesImported.includes('logic')) {
            alert('cannot magic the AND, since logic not imported');
            return '';
        }
        const myArgs = s.split(' ');
        const sentence = myArgs[1];
        const parsed = parseTerm(sentence);
        if (parsed.error) return '';
        const seenAlready = parsed.free.concat(parsed.bound);
        let newVar = 'y';
        let count = 0;
        while (seenAlready.includes(newVar)) {
            newVar = 'y' + count;
            count ++;
        }
        let newVar1 = 'y' + count;
        while (seenAlready.includes(newVar1)) {
            count ++;
            newVar1 = 'y' + count;
        }
        const frees = myArgs[2] ? myArgs[2].split(',') : parsed.free;
        const revFrees = frees.map(x=>x).reverse();
        const myGen = myArgs[3] || 'P';
        const assumption = frees.map(v => 'A'+v+'(').join('') + 'A' + newVar + '((' + myGen + '[' + frees.join(',') + ',' + newVar + '])<>((' + newVar + ')=(' + sentence + ')))' + frees.map(v => ')').join('');
        console.log(assumption);
        var def = globalProver.Assume(assumption);
        const specAssumption = doTransforms([def].concat(frees.flatMap(v => ['SV', v])).concat(['SV', newVar]));
        var subbed = globalProver.SubConnective(specAssumption, '<>', globalProver.statements.get(specAssumption).p.sentence.indexOf('<>'));
        const subbedParsed = globalProver.statements.get(subbed).p.parsed;
        if (subbedParsed[0] != '&&') {
            alert('Expected &&, got ' + subbedParsed[0]);
            return '';
        }
        const imp1 = subbedParsed[2][0].sentence;
        const imp2 = subbedParsed[2][1].sentence;
        const ae1 = globalProver.Quote('and_elimination1');
        const ae2 = globalProver.Quote('and_elimination2');
        const temp1 = doTransforms([ae1, 'S', 'P', 'P123', 'S', 'Q', 'Q123', 'S', 'P123', imp1, 'S', 'Q123', imp2]);
        const temp2 = doTransforms([ae2, 'S', 'P', 'P123', 'S', 'Q', 'Q123', 'S', 'P123', imp1, 'S', 'Q123', imp2]);
        const fromP = globalProver.MP(temp1, subbed);
        const toP = globalProver.MP(temp2, subbed);
        const toPSubbed = doTransforms([toP, 'G', newVar, 'SV', sentence]);
        console.log(toP, toPSubbed);
        const x = doTransforms([4, 'SV', sentence, 'MP', toPSubbed, 'GE', 'E' + newVar + '(' + myGen + '[' + frees.join(',') + ',' + newVar + '])']);
        const x1 = doTransforms([x].concat(revFrees.flatMap(v => ['G', v])));
        for (const k of [subbed, ae1, ae2, temp1, temp2, toP, toPSubbed, x]) deleteStatement(k);
        const a1 = globalProver.Assume(myGen + '[' + frees.join(',') + ',' + newVar + ']');
        const a2 = globalProver.Assume(myGen + '[' + frees.join(',') + ',' + newVar1 + ']');
        const eq1 = doTransforms([fromP, 'MP', a1]); // y=sentence
        const eq2 = doTransforms([fromP, 'G', newVar, 'SV', newVar1, 'MP', a2]); // y0=sentence
        const eq3 = doTransforms([4, 'SV', newVar]); // y=y
        const eq4 = doTransforms([5, 'S', 'P', '(@)=(' + newVar + ')', 'SV', newVar, 'SV', sentence, 'MP', eq1, 'MP', eq3]); // sentence=y 
        const i5 = doTransforms([5, 'S', 'P', '(' + newVar1 + ')=(@)', 'SV', sentence, 'SV', newVar, 'MP', eq4, 'MP', eq2]);
        const x2 = globalProver.DT(a1, i5);
        const x3 = globalProver.DT(a2, x2);
        const x4 = doTransforms([x3, 'G', newVar, 'G', newVar1].concat(revFrees.flatMap(v => ['G', v])));
        for (const k of [a1, a2, eq1, eq2, eq3, eq4, i5, x2, x3, fromP, specAssumption]) deleteStatement(k);
        const ai = globalProver.Quote('and_introduction');
        const functionPred = frees.length == 1 ? "func" : ("func" + frees.length);
        const x5 = doTransforms([ai, 'S', 'P', 'P123', 'S', 'Q', 'Q123',
            'S', 'P123', globalProver.statements.get(x1).p.sentence,
            'S', 'Q123', globalProver.statements.get(x4).p.sentence,
            'MP', x1, 'MP', x4, 'Rewrite', "'" + functionPred + "[" + myGen + ";]"]);
        const result = globalProver.DT(def, x5);
        for (const k of [ai, x1, x4, x5, def]) deleteStatement(k);
        updatePage();
        return '';
    }
    if (s.startsWith('!sub ')) {
        var id = +s.slice(5);
        var s = globalProver.statements.get(id);
        if (!s) return '';
        var P = s.p.parsed;
        if (P[0] != '=') return '';
        const t1 = P[2][0].sentence, t2 = P[2][1].sentence;
        const toSub = prompt('Term to substitute:');
        if (!toSub) return '';
        var pst = parseTerm(toSub, true);
        if (!pst.error) {
            const toSub1 = toSub.replaceAll('@', t1);
            console.log('user subbing term:', t1, t2, toSub, toSub1);
            var temp1 = globalProver.SV(4, toSub1);
            var temp5 = doTransforms([5, 'S', 'P', 'P123', 'SV', t1, 'SV', t2, 'S', 'P123', '('+toSub1+')=('+toSub+')']);
            var temp6 = globalProver.MP(temp5, id);
            var temp7 = globalProver.MP(temp6, temp1);
            for (var k of [temp1, temp5, temp6]) deleteStatement(k);
            updatePage();
            return '';
        }
        pst = parseSentence(toSub, true);
        if (!pst.error) {
            console.log('user subbing sentence:', t1, t2, toSub);
            var temp1 = doTransforms([5, 'S', 'P', 'P123', 'SV', t1, 'SV', t2, 'S', 'P123', toSub]);
            var temp5 = globalProver.MP(temp1, id);
            deleteStatement(temp1);
            updatePage();
            return '';
        }
        alert('Could not parse ' + toSub + ' as either a sentence or a term')
        return '';
    }
    if (s.startsWith('!newrel ')) {
        let [_, name, termArity, predArity, sentence] = s.split(' ');
        console.log(sentence);
        termArity = +termArity;
        predArity = +predArity;
        if (name[0] != "'") name = "'" + name;
        globalProver.AddRelation(termArity, name, sentence, predArity);
        updatePage();
        return '';
    }
    if (s.startsWith('!want ')) {
        const sentence = s.slice(6);
        const parsed = parseSentence(sentence);
        userAddWanted(parsed, new Set());
        userUpdateDisplay();
        return '';
    }
    if (s.startsWith('! ')) {
        var id = +s.slice(2);
        if (!id) {
            const p = parseTerm(s.slice(2));
            if (p.error) return '';
            termToRewrite(s.slice(2));
            return '';
        }
        var s = globalProver.statements.get(id);
        if (!s) return '';
        var P = s.p.parsed;
        if (P[0] == '=>' && P[2][1].sentence == 'F' && P[2][0].parsed[0] == '=>' && P[2][0].parsed[2][1].sentence == 'F') {
            var temp1 = doTransforms([3, 'S', 'P', P[2][0].parsed[2][0].sentence]);
            var temp2 = globalProver.MP(temp1, id);
            deleteStatement(temp1);
        } else if (P[0] == '=>' && P[2][1].sentence == 'F' && P[2][0].parsed[0] == '=>') {
            const a = P[2][0].parsed[2][0].sentence, b = P[2][1].parsed[2][1].sentence;
            var notA = globalProver.Assume('('+a+')=>(F)');
            var yesA = globalProver.Assume(a);
            var exp = globalProver.Quote('explosion');
            var yesB = globalProver.S(exp, 'P', b);
            var False = globalProver.MP(notA, yesA);
            var thusB = globalProver.MP(yesB, False);
            var AsoB = globalProver.DT(yesA, thusB);
            var contradiction = globalProver.MP(id, AsoB);
            var notNotA = globalProver.DT(notA, contradiction);
            var lemA = globalProver.S(3, 'P', a);
            var finallyA = globalProver.MP(lemA, notNotA);
            var assumeB = globalProver.Assume(b);
            var aSoB2 = globalProver.DT(finallyA, assumeB);
            var cont2 = globalProver.MP(id, aSoB2);
            var finallyNotB = globalProver.DT(assumeB, cont2);
            for (var k of [notA, yesA, exp, yesB, False, thusB, AsoB, contradiction, notNotA, lemA, assumeB, aSoB2, cont2])
                deleteStatement(k);
        } else if (P[0] == '&&') {
            splitAnd(id);
        } else if (P[0] == '||') {
            if (!globalProver.filesImported.includes('logic')) {
                alert('cannot magic the OR, since logic not imported');
                return '';
            }
            var possibilities = [];
            for (const [i,s] of globalProver.statements.entries()) {
                if (s.p.parsed[0] != '=>') continue;
                if (s.deleted) continue;
                if (s.p.parsed[1] == P[1]) possibilities.append([i, 1, s.p.parsed[2]]);
                else if (s.p.parsed[1] == P[2]) possibilities.append([i, 2, s.p.parsed[2]]);
            }
        }
        updatePage();
        return '';
    }
    if (s === '!reset') return completeReset();
    // do some tidying to the input string
    return '';
}
window.userOnProof = function (s) {
    if (!userWants.has(s.p.sentence)) return;
    var x = userWants.get(s.p.sentence);
    var assumptions = new Set(x[2]);
    if (!s.deps.every(d => assumptions.has(globalProver.statements.get(d).p.sentence))) return;
    x[0] = 'proved';
    userUpdateDisplay();
}
function userRemoveWanted(sentence) {
    if (!confirm('are you sure?')) return;
    userWants.delete(sentence);
    userUpdateDisplay();
}
function userAddWanted(parsed, assumptions) {
    if (parsed.error) {
        alert(parsed.error);
        return;
    }
    assumptions = new Set(assumptions);
    const alreadyProved = someEntry(globalProver.statements,
        (k,v)=>v.p.sentence == parsed.sentence && v.deps.every(d => assumptions.has(globalProver.statements.get(d).p.sentence)));
    userWants.set(parsed.sentence, [alreadyProved ? 'proved' : 'unknown', renderParsed(parsed), [...assumptions]]);
}
function userCopyStatement(sentence) {
    navigator.clipboard.writeText(sentence);
}
function userUpdateDisplay() {
    var outputLines = [];
    for (var [sentence, [state, rendered, assumptions]] of userWants.entries()) {
        var style = state == 'proved' ? "color:green;background-color:#cfc" : 'color:black;background-color:#fcc';
        outputLines.push('<tr style="'+style+'">' +
        '<td><button onclick="userRemoveWanted(\'' + sentence.replaceAll("'", "\\'") + '\')">x</button></td>' +
        '<td><button onclick="userCopyStatement(\'' + sentence.replaceAll("'", "\\'") + '\')">&#9986;</button></td>' +
        '<td><button onclick="userInduct(\'' + sentence.replaceAll("'", "\\'") + '\')">ind</button></td>' +
        '<td><button onclick="userInduct(\'' + sentence.replaceAll("'", "\\'") + '\', true)">sind</button></td>' +
        '<td><button onclick="userDirect(\'' + sentence.replaceAll("'", "\\'") + '\')">dir</button></td>' +
        '<td><button onclick="userMP(\'' + sentence.replaceAll("'", "\\'") + '\')">&rArr;</button></td>' +
        '<td>' + rendered + '</td>' + 
        '<td style="font-weight:bold;color:gray">' + [...assumptions]
        //.map(sentence => renderParsed(parseSentence(sentence)))
        .join(', ')+ '</td>' +
        '</tr>');
        // &#9744; unchecked, &#9745; checked
    }
    const finalOutput = ('<table>' + outputLines.join('') + '</table>');
    //console.log(finalOutput);
    document.getElementById('userStuff').innerHTML = finalOutput;
    localStorage.setItem('userWants', JSON.stringify([...userWants]));
}
function userDirect(sentence) {
    var parsed = parseSentence(sentence);
    if (parsed.error) return alert('parsing error (this should never happen...)');
    if (parsed.parsed[0] != 'A') return alert('cannot direct, must start with forall');
    userAddWanted(parsed.parsed[2], userWants.get(sentence)[2]);
    userUpdateDisplay();
}
function userMP(sentence) {
    var parsed = parseSentence(sentence);
    if (parsed.error) return alert('parsing error (this should never happen...)');
    if (parsed.parsed[0] != '=>') return alert('must be of the form P=>Q');
    userAddWanted(parsed.parsed[2], userWants.get(sentence)[2].concat([parsed.parsed[1].sentence]));
    userUpdateDisplay();
}
function userInduct(sentence, strong=false) {
    var parsed = parseSentence(sentence);
    if (parsed.error) return alert('parsing error (this should never happen...)');
    if (parsed.parsed[0] != 'A') return alert('cannot induct, must start with forall');
    // rewrite to make it Ax(...)

    const x = parsed.parsed[1];
    const error = undefined;
    const rewrittenParsed = parsed;
    if (error) {
        alert(error);
        return;
    }
    if (rewrittenParsed.error) {
        alert(rewrittenParsed.error);
        return;
    }
    const innerParsed = rewrittenParsed.parsed[2];
    const assumptions = userWants.get(sentence)[2];
    if (!strong) {
        const [sub0, e0] = globalProver.rewriteSentence(innerParsed, new Map([[x, parseTerm('0')]]));
        const subx = innerParsed;
        const [subSx, eSx] = globalProver.rewriteSentence(innerParsed, new Map([[x, parseTerm('S('+x+')')]]));
        if (eSx) return alert(eSx);
        const inductionSentence = 'A'+x+'((' + subx.sentence + ')=>(' + subSx.sentence + '))';
        userAddWanted(sub0, assumptions);
        userAddWanted(parseSentence(inductionSentence), assumptions);
    } else {
        const y = getNewVarname(rewrittenParsed, 'y');
        const [suby, ey] = globalProver.rewriteSentence(innerParsed, new Map([[x, parseTerm(y)]]));
        const Py = suby.sentence;
        const Px = innerParsed.sentence;
        const inductionSentence = `A${x}((A${y}(((${y})<(${x}))=>(${Py})))=>(${Px}))`;
        userAddWanted(parseSentence(inductionSentence), assumptions);
    }
    userUpdateDisplay();
}
window.userOnLoad = function() {
    //console.log('user on load', userWants, localStorage.getItem('userWants'));
    if (userWants.size == 0 && localStorage.getItem('userWants'))
        userWants = new Map(JSON.parse(localStorage.getItem('userWants')));
    userUpdateDisplay();
}
function userReset() {
    if (!confirm('are you sure?')) return;
    userWants = new Map();
    userUpdateDisplay();
}
