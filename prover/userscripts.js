'use strict';
function alreadyProved(sentence) {
    for (const [i,s] of globalProver.statements.entries()) {
        if (s.p.sentence === sentence) return true;
    }
    return false;
}
var DEL = true;
var userWants = new Map();
function doTransforms(arr) {
    var currentStatement = arr[0];
    for (var i = 1; i < arr.length; ++ i) { 
        if (arr[i] == 'SV') {
            var variable = arr[i+1];
            if (variable == 'new') variable = 't85383';
            var temp = globalProver.SV(currentStatement, variable);
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
        } else throw new Error('asdfasdfasdfassad');
    }
    return currentStatement;
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
        var temp1 = doTransforms([ai, 'S', 'P', a, 'S', 'Q', b]);
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
    if (s === '!==') {
        for (const [i,s] of globalProver.statements.entries()) {
            if (s.p.parsed[0] != '=') continue;
            if (s.deleted || !s.highlight) continue;
            const sp = s.p.parsed;
            const u = sp[1].sentence, v = sp[2].sentence;
            if (u == v) continue;
            var temp = doTransforms([5, 'SV', u, 'SV', v, 'S', 'P', `(@)=(${u})`]);
            var temp2 = globalProver.SV(4, u); // u=u
            var temp3 = globalProver.MP(temp, i);
            var temp4 = globalProver.MP(temp3, temp2);
            deleteStatement(temp);
            deleteStatement(temp2);
            deleteStatement(temp3);
        }
        updatePage();
        return '';
    }
    if (s === '!=') {
        for (const [i,s] of globalProver.statements.entries()) {
            if (s.p.parsed[0] != '=') continue;
            if (s.deleted || !s.highlight) continue;
        for (const [j,t] of globalProver.statements.entries()) {
            if (t.deleted || !t.highlight) continue;
            if (i === j) continue;
            var sp = s.p.parsed, tp = t.p.parsed;
            if (tp[0] == '!=') {
                // s: u=v or v=u, t: v!=w or w!=v
                continue;
            }
            if (sp[0] != '=' || tp[0] != '=') continue;
            // s: V1=V2, t: V2=V3
            if (sp[2].sentence == tp[1].sentence) {
                var u = sp[1].sentence, v = sp[2].sentence, w = tp[2].sentence;
                if (u == w) continue;
                //if (alreadyProved(`(${u})=(${w})`)) continue;
                var temp6 = doTransforms([5, 'SV', v, 'SV', w, 'S', 'P', `(${u})=(@)`]);
                var temp3 = globalProver.MP(temp6, j);
                var temp4 = globalProver.MP(temp3, i);
                deleteStatement(temp3);
                deleteStatement(temp6);
            } else if (sp[1].sentence == tp[1].sentence) {
                var u = sp[1].sentence, v = sp[2].sentence, w = tp[2].sentence;
                if (v == w) continue;
                //if (alreadyProved(`(${v})=(${w})`)) continue;
                var i5 = doTransforms([5, 'SV', u, 'SV', v, 'S', 'P', `(@)=(${w})`]);
                var i6 = globalProver.MP(i5, i);
                var i7 = globalProver.MP(i6, j);
                for (var k of [i5, i6])
                    deleteStatement(k);
            } else if (sp[2].sentence == tp[2].sentence) {
                var u = sp[1].sentence, v = sp[2].sentence, w = tp[1].sentence;
                if (u == w) continue;
                //if (alreadyProved(`(${u})=(${w})`)) continue;
                var b1 = doTransforms([5, 'SV', w, 'SV', v, 'S', 'P', `(@)=(${w})`]);
                var temp1 = globalProver.SV(4, w); // w=w
                var temp4 = globalProver.MP(b1, j); // w=w => v=w
                var temp5 = globalProver.MP(temp4, temp1); // v=w
                var b2 = doTransforms([5, 'SV', v, 'SV', w, 'S', 'P', `(${u})=(@)`]);
                var temp9 = globalProver.MP(b2, temp5);
                var temp10 = globalProver.MP(temp9, i); // u=w
                for (var k of [b1, temp1, temp4, temp5, b2, temp9])
                    deleteStatement(k);
            }
        }}
        updatePage();
        return '';
    }
    if (s === '!t') {
        const theoremName = prompt('What theorem? You know ' + [...globalProver.knownTheorems.keys()]);
        if (!theoremName) return '';
        if (!globalProver.knownTheorems.has(theoremName)) alert('Unknown theorem');
        globalProver.Quote(theoremName);
        updatePage();
        return '';
    }
    if (s.startsWith('!sub ')) {
        var id = +s.slice(5);
        var s = globalProver.statements.get(id);
        if (!s) return '';
        var P = s.p.parsed;
        if (P[0] != '=') return '';
        const t1 = P[1].sentence, t2 = P[2].sentence;
        const toSub = prompt('Term to substitute:');
        if (!toSub) return '';
        var pst = parseTerm(toSub, true);
        if (!pst.error) {
            const toSub1 = toSub.replaceAll('@', t1);
            console.log('user subbing term:', t1, t2, toSub, toSub1);
            var temp1 = globalProver.SV(4, toSub1);
            var temp5 = doTransforms([5, 'SV', t1, 'SV', t2, 'S', 'P', '('+toSub1+')=('+toSub+')']);
            var temp6 = globalProver.MP(temp5, id);
            var temp7 = globalProver.MP(temp6, temp1);
            for (var k of [temp1, temp5, temp6]) deleteStatement(k);
            updatePage();
            return '';
        }
        pst = parseSentence(toSub, true);
        if (!pst.error) {
            console.log('user subbing sentence:', t1, t2, toSub);
            var temp1 = doTransforms([5, 'SV', t1, 'SV', t2, 'S', 'P', toSub]);
            var temp5 = globalProver.MP(temp1, id);
            deleteStatement(temp1);
            updatePage();
            return '';
        }
        alert('Could not parse ' + toSub + ' as either a sentence or a term')
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
        console.log(P);
        if (P[0] == '=>' && P[2].sentence == 'F' && P[1].parsed[0] == '=>' && P[1].parsed[2].sentence == 'F') {
            var temp1 = doTransforms([3, 'S', 'P', P[1].parsed[1].sentence]);
            var temp2 = globalProver.MP(temp1, id);
            deleteStatement(temp1);
        } else if (P[0] == '=>' && P[2].sentence == 'F' && P[1].parsed[0] == '=>') {
            const a = P[1].parsed[1].sentence, b = P[1].parsed[2].sentence;
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
            if (!globalProver.filesImported.includes('logic')) {
                alert('cannot magic the AND, since logic not imported');
                return '';
            }
            var s1 = P[1].sentence, s2 = P[2].sentence;
            var ae1 = globalProver.Quote('and_elimination1');
            var ae2 = globalProver.Quote('and_elimination2');
            var temp1 = doTransforms([ae1, 'S', 'P', s1, 'S', 'Q', s2]);
            var final1 = globalProver.MP(temp1, id);
            var temp2 = doTransforms([ae2, 'S', 'P', s1, 'S', 'Q', s2]);
            var final2 = globalProver.MP(temp2, id);
            for (var k of [ae1, ae2, temp1, temp2]) deleteStatement(k);
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
