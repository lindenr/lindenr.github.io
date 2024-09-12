"use strict";
function later(f, ...args) {
    setTimeout(function(){f(...args);});
    return false;
}
function someEntry(x, f) {
    for (const [key, value] of x.entries()) {
        if (f(key, value)) return true;
    }
    return false;
}
function uniSort(arr) {
    if (typeof arr === 'object') arr = [... arr];
    if (arr.length == 0) return arr;
    if (typeof arr[0] === 'string') return [...new Set(arr)].sort();
    if (typeof arr[0] === 'number') return [...new Set(arr)].sort((a,b)=>a-b);
    alert('UNKNOWN TYPE OF ' + arr[0]);
    throw new Error('asdfasdfasdf');
}
function arrayEqual(a1, a2) {
    if (a1.length != a2.length) return false;
    if (a1.length == 0) return true;
    a1 = uniSort(a1);
    a2 = uniSort(a2);
    for (var i = 0; i < a1.length; ++ i) if (a1[i] !== a2[i]) return false;
    return true;
}
function sortedIntersection(a1, a2) { // ASSUMES SORTED
    var i = 0;
    for (var x1 of a1) {
        while (i < a2.length && a2[i] < x1) ++ i;
        if (i < a2.length && x1 == a2[i]) return true;
    }
    return false;
}
function matchingBracket(s, i) {
    const brackets = new Map([['[', ']'], ['(', ')'], ['{', '}']]);
    const closeBrackets = new Set([']', ')', '}']);
    if (!brackets.has(s[i])) return -1;
    var bracketsSeen = [s[i]];
    for (var j = i+1; j < s.length; ++ j) {
        if (brackets.has(s[j])) {
            bracketsSeen.push(s[j]);
        } else if (closeBrackets.has(s[j])) {
            if (brackets.get(bracketsSeen[bracketsSeen.length-1]) != s[j]) return -1;
            bracketsSeen.pop();
            if (bracketsSeen.length == 0) return j;
        }
    }
    return -1;
}
function matchingBracketReverse(s,i) {
    const brackets = new Map([[']', '['], [')', '('], ['}', '{']]);
    const closeBrackets = new Set(['[', '(', '{']);
    if (!brackets.has(s[i])) return -1;
    var bracketsSeen = [s[i]];
    for (var j = i-1; j >= 0; -- j) {
        if (brackets.has(s[j])) {
            bracketsSeen.push(s[j]);
        } else if (closeBrackets.has(s[j])) {
            if (brackets.get(bracketsSeen[bracketsSeen.length-1]) != s[j]) return -1;
            bracketsSeen.pop();
            if (bracketsSeen.length == 0) return j;
        }
    }
    return -1;
}
// operators: we always have =
// support arity 0, 1, 2; 1-arity always prefix, 2-arity always infix
const BASEOPERATORS = [['0'], ['S'], ['+', '*']]; // e.g. exponentiation
const BASERELATIONS = [[], [], ['='], []]; // e.g. isPrime, <
const BASECONNECTIVES = [[], [], ['=>']]; // e.g. not, and, or
var OPERATORS = [['0'], ['S'], ['+', '*']]; // e.g. exponentiation
var RELATIONS = [[], [], ['='], []]; // e.g. isPrime, <
var CONNECTIVES = [[], [], ['=>']]; // e.g. not, and, or
const AXIOMS = [
    ['(P)=>((Q)=>(P))', 'A1. Anything implies truth'],
    ['((P)=>((Q)=>(R)))=>(((P)=>(Q))=>((P)=>(R)))', 'A2. Implication under conditions'],
    ['(((P)=>(F))=>(F))=>(P)', 'A3. Law of excluded middle'],
    ['Ax((x)=(x))', 'A4. Self-equality'],
    ['Ax(Ay(((x)=(y))=>((P[x])=>(P[y]))))', 'A5. Substitutability of equal terms'],
    ['Ay((Ax(P[x]))=>(P[y]))', 'A6. Generic example from universal'],
    ['(Ax((P)=>(Q)))=>((P)=>(Ax(Q)))', 'A7. Specialisation of forall quantifier'],
    ['Ax(Ay(((S(x))=(S(y)))=>((x)=(y))))', 'PA1. Injectivity of S'],
    ['Ax(((S(x))=(0))=>(F))', 'PA2. 0 is not a successor'],
    ['Ax(((x)+(0))=(x))', 'PA3. 0 is the additive identity'],
    ['Ax(Ay(((x)+(S(y)))=(S((x)+(y)))))', 'PA4. Addition commutes with S'],
    ['Ax(((x)*(0))=(0))', 'PA5. Multiplication by 0'],
    ['Ax(Ay(((x)*(S(y)))=(((x)*(y))+(x))))', 'PA6. Distributivity of addition'],
    ['(P[0])=>((Ax((P[x])=>(P[S(x)])))=>(Ax(P[x])))', 'PA7. Induction'],
    ];
function isGeneric(gen) {
    return gen[0] >= 'P' && gen[0] <= 'R' && /^\d*$/.test(gen.slice(1));
}
function isSubstitutionInstanceOf(s1, s2) {
    // is s1 the same as s2 but where you can put in anything you like for the @ variables in s2, and also can rename bound variables?
}
// if permissive, allow @, @0, etc as variables
function parseVariable(sentence, permissive=false) {
    if (sentence[0] >= 'a' && sentence[0] <= 'z' && /^\d*$/.test(sentence.slice(1)))
    {
        return parsedSentence(sentence, [sentence], [], [sentence], [], undefined, false);
    }
    if (sentence[0] == '#' && sentence[1] >= 'a' && sentence[1] <= 'z' && /^\d*$/.test(sentence.slice(2)))
    {
        return parsedSentence(sentence, [sentence], [], [sentence], [], undefined, false);
    }
    if (permissive && sentence[0] == '@' && /^\d*$/.test(sentence.slice(1)))
    {
        return parsedSentence(sentence, [sentence], [], [sentence], [], undefined, false);
    }
    return false;
}
// a parsed sentence is one of:
// ["A", <var>, Parsed], ["E", <var>, Parsed], [<rel>, Terms], [<conn>, Parsed's], [<gen>], [<gen>, <repl>]
// term:
// [<var>], [<op>, Terms]
function parseError(sentence, error) {
    return {parsed: undefined, error: error, sentence: sentence, bound: [], free: [], brackets: true, generics: []};
}
function parsedSentence(sentence, parsed, bound, free, generics, error, brackets=true) {
    return {parsed: parsed, bound: bound, free: free, sentence: sentence, generics: uniSort(generics), error: error, brackets: brackets};
}
function parseTerm(sentence, permissive=false) {
    var length = sentence.length;
    if (sentence === '') return parseError(sentence, 'empty string');
    if (OPERATORS[1].includes(sentence[0]))
    {
        if (sentence[1] != '(' || sentence[length-1] != ')') return parseError(sentence, 'operand must be bracketed');
        var subResult = parseTerm(sentence.slice(2, length-1), permissive);
        return parsedSentence(sentence, [sentence[0], subResult], subResult.bound, subResult.free, [], subResult.error, false);
    }
    if (sentence[0] == '(')
    {
        var i = matchingBracket(sentence, 0);
        if (i == -1) return parseError(sentence, 'brackets not closed');
        if (length < i+4) return parseError(sentence, 'expect an operator after brackets');
        if (sentence[i+1] == '(') return parseError(sentence, 'missing operator');
        var operator_length = 0;
        if (sentence[i+2] == '(') operator_length = 1;
        else if (sentence[i+3] == '(') operator_length = 2;
        else return parseError(sentence, 'operator too long or missing brackets after operator');
        if (sentence[length-1] != ')') return parseError(sentence, 'must end with close bracket');
        var op1 = parseTerm(sentence.slice(1, i), permissive);
        var op2 = parseTerm(sentence.slice(i + 1 + operator_length + 1, length-1), permissive);
        var newBound = uniSort(op1.bound.concat(op2.bound));
        var newFree = uniSort(op1.free.concat(op2.free));
        var operator = sentence.slice(i+1, i+1+operator_length);
        if (!(OPERATORS[2].includes(operator)))
        {
            return parseError(sentence, 'term operator not recognized: "'+operator+'"');
        }
        return parsedSentence(sentence, [operator, op1, op2], newBound, newFree, [], op1.error || op2.error);
    }
    if (length == 1 && OPERATORS[0].includes(sentence[0]))
    {
        return parsedSentence(sentence, [sentence], [], [], [], undefined, false);
    }
    var parsed = parseVariable(sentence, permissive);
    if (parsed) return parsed;
    return parseError(sentence, "expect terms to start with '(', an arity-1 operator, or be a primitive value");
}
function parseSentence(sentence, permissive=false) {
    var length = sentence.length;
    if (sentence == 'F') return parsedSentence(sentence, ["F"], [], [], [], undefined, false);
    if (sentence === '') return parseError(sentence, 'empty string');
    if (sentence[0] == 'A' || sentence[0] == 'E')
    {
        if (length < 5) return parseError(sentence, 'unknown string');
        const j = sentence.indexOf('(');
        if (j == -1) return parseError(sentence, 'expected open paren');
        var newVar = sentence.slice(1, j);
        if (!parseVariable(newVar, permissive)) return parseError(sentence, 'invalid variable ' + newVar);
        if (newVar[0] == '#') return parseError(sentence, 'cannot bind a defined variable (one that begins with #)');
        if (sentence[length - 1] != ')') return parseError(sentence, 'should end with close paren');
        var subResult = parseSentence(sentence.slice(j+1, length - 1), permissive);
        if (subResult.bound.includes(newVar)) return parseError(sentence, 'newly bound variable already bound');
        var newBound = uniSort(subResult.bound.concat(newVar));
        var newFree = subResult.free.slice();
        var i = newFree.indexOf(newVar);
        if (i >= 0) newFree.splice(i, 1);
        return parsedSentence(sentence, [sentence[0], newVar, subResult], newBound, newFree, subResult.generics, subResult.error);
    }
    if (sentence[0] == '(')
    {
        var i = matchingBracket(sentence, 0);
        if (i == -1) return parseError(sentence, 'brackets not closed');
        if (length < i+4) return parseError(sentence, 'expect an operator after brackets');
        if (sentence[i+1] == '(') return parseError(sentence, 'missing operator');
        var operator_length = 0;
        if (sentence[i+2] == '(') operator_length = 1;
        else if (sentence[i+3] == '(') operator_length = 2;
        else return parseError(sentence, 'operator too long or missing brackets after operator');
        if (sentence[length-1] != ')') return parseError(sentence, 'must end with close bracket');
        var operator = sentence.slice(i+1, i+1+operator_length);
        var op1, op2;
        if (CONNECTIVES[2].includes(operator)) {
            op1 = parseSentence(sentence.slice(1, i), permissive);
            op2 = parseSentence(sentence.slice(i + 1 + operator_length + 1, length - 1), permissive);
        } else if (RELATIONS[2].includes(operator)) {
            op1 = parseTerm(sentence.slice(1, i), permissive);
            op2 = parseTerm(sentence.slice(i + 1 + operator_length + 1, length - 1), permissive);
        } else return parseError(sentence, 'operator not recognized: "'+operator+'"');
        if (sortedIntersection(op1.bound, op2.free) || sortedIntersection(op2.bound, op1.free))
        {
            return parseError(sentence, 'can\'t have a variable be both bound and free');
        }
        var newBound = uniSort(op1.bound.concat(op2.bound));
        var newFree = uniSort(op1.free.concat(op2.free));
        var newGenerics = uniSort(op1.generics.concat(op2.generics));
        return parsedSentence(sentence, [operator, op1, op2], newBound, newFree, newGenerics, op1.error || op2.error);
    }
    if (sentence[0] >= 'P' && sentence[0] <= 'R')
    {
        const i = sentence.indexOf('[');
        if (i == -1) {
            if (isGeneric(sentence)) return parsedSentence(sentence, [sentence], [], [], [sentence], undefined, false);
            return parseError(sentence, 'unrecognised generic');
        }
        if (sentence[sentence.length-1] != ']') return parseError(sentence, 'unrecognised generic');
        const gen = sentence.slice(0, i);
        if (!isGeneric(gen)) return parseError(sentence, 'unrecognised generic');
        var interior = sentence.slice(i+1, -1);
        var terms = interior.split(',');
        var ips = terms.map(t => parseTerm(t, permissive));
        const frees = uniSort(ips.flatMap(pt => pt.free));
        const error = ips.filter(pt => pt.error !== undefined).map(x => x.error)[0];
        return parsedSentence(sentence, [gen, ...ips], [], frees, [gen], error, false);
    }
    if (sentence[0] == "'") {
        // prefix relation
        const i = sentence.indexOf('[');
        if (i == -1) return parseError(sentence, 'relation must have square brackets');
        if (sentence[sentence.length-1] != ']') return parseError(sentence, 'unrecognised relation')
        const relation = sentence.slice(0, i);
        var terms = sentence.slice(i+1, -1).split(','); // assumes terms can't have commas...
        const arity = terms.length;
        if (!RELATIONS[arity].includes(relation)) return parseError(sentence, 'unrecognised relation');
        var ips = terms.map(t => parseTerm(t, permissive));
        const frees = uniSort(ips.flatMap(pt => pt.free));
        const error = ips.filter(pt => pt.error !== undefined).map(x=>x.error)[0];
        return parsedSentence(sentence, [relation, ...ips], [], frees, [], error, false);
    }
    return parseError(sentence, 'expect a sentence to start with "A" or "("');
}
function renderOperator(op) {
    if (op === "=>") return "&rArr;";
    if (op === "<=") return "&leq;";
    if (op === '+') return "&plus;";
    if (op === '*') return "&sdot;";
    if (op === '&&') return "&and;";
    if (op === '||') return "&or;";
    if (op === '!=') return "&ne;";
    if (op === '<') return "&lt;";
    if (op === '!<') return "&nlt;";
    return op;
}
function brender(parsed, statementId=-1, where=0) {
    if (parsed.brackets) return "(" + renderParsed(parsed, statementId, where) + ")";
    return renderParsed(parsed, statementId, where);
}
function renderParsed(parsed, statementId=-1, where=0) {
    // is there an error on this level
    if (parsed.parsed == undefined) return '<b style="color:red">' + parsed.sentence + '</b>';
    var p = parsed.parsed;
    if (p[0] == "F") return "&perp;";
    if (p[0] == "A") return "&forall;" + p[1] + " (" + renderParsed(p[2], statementId, where+1+p[1].length+1) + ")";
    if (p[0] == "E") return "&exist;" + p[1] + " (" + renderParsed(p[2], statementId, where+1+p[1].length+1) + ")";
    if (p[0] >= 'P' && p[0] <= 'R') {
        var starter = (statementId >= 0 ? '<a href="#" onclick="return later(specStatement, ' + statementId + ', \'' + p[0] + '\')">' : '');
        var ender = statementId >= 0 ? '</a>' : '';
        if (p.length == 1) return starter + p[0] + ender;
        return starter + p[0] + '[' + p.slice(1).map(tp => renderParsed(tp, statementId, 0)).join(',') + ']' + ender;
    }
    if (statementId >= 1 && globalProver.orcMap.has(p[0])) {
        const [typename, arity, defn] = globalProver.orcMap.get(p[0]);
        if (defn != undefined && arity == 2 && p[0][0] != "'") {
            return brender(p[1], statementId, where+1) + '<a href="#" onclick="return later(expandSymbol, ' + statementId + ', \'' + p[0] + '\', ' + (where+1+p[1].sentence.length+1) + ')">' + renderOperator(p[0]) + '</a>' + brender(p[2], statementId, where+1+p[1].sentence.length+1+p[0].length+1);
        } else if (defn != undefined && p[0][0] == "'") {
            var soFar = '<a href="#" onclick="return later(expandSymbol, ' + statementId + ', \'\\' + p[0] + '\', ' + (where) + ')" style="font-style:italic">'+p[0].slice(1) + '</a>[';
            var currentWhere = where + p[0].length + 1;
            for (var i = 1; i < p.length; ++ i) {
                const p0 = p[i];
                soFar += renderParsed(p0, statementId, currentWhere)+',';
                currentWhere + p0.sentence.length+1;
            }
            return soFar.slice(0,soFar.length-1) + ']';
        }
    }
    if (p[0][0] == "'") return p[0].slice(1) + '[' + p.slice(1).map(p0 => renderParsed(p0, statementId)).join(',') + ']';
    if (p.length == 1) return p[0];
    if (p.length == 2) return p[0] + brender(p[1], statementId, where+p[0].length+1);
    if (p.length == 3)
        return brender(p[1], statementId, where+1) + renderOperator(p[0]) + brender(p[2], statementId, where+1+p[1].sentence.length+1+p[0].length+1);
    console.log(parsed);
    throw new Error('reached end of renderParsed');
}
function renderSentence(sentence) {
    return '<b>'+renderParsed(parseSentence(sentence))+'</b>';
}
function renderClickable(statement) {
    var parsed = statement.p;
    var result = renderParsed(parsed, statement.id);
    if (parsed.parsed[0] == 'A') {
        result = '<a href="#" onclick="return later(specialiseForall, globalProver.statements.get('+statement.id+'))">' + result.slice(0, 10+parsed.parsed[1].length) + '</a>' + result.slice(10+parsed.parsed[1].length);
    } else if (parsed.parsed[0] == 'E') {
        result = '<a href="#" onclick="return later(specialiseExists, globalProver.statements.get('+statement.id+'))">' + result.slice(0, 10+parsed.parsed[1].length) + '</a>' + result.slice(10+parsed.parsed[1].length);
    }
    if (!statement.proved) {
        result = '<b style="background-color:#fbb">' + result + '</b>';
    }
    return result;
}
function getNewVarname(parsed, startingLetter, disallowedVars=[]) {
    disallowedVars = new Set(parsed.free.concat(parsed.bound).concat([...disallowedVars]));
    if (!disallowedVars.has(startingLetter)) return startingLetter;
    var i = 0;
    while (disallowedVars.has(startingLetter+i)) ++ i;
    return startingLetter+i;
}
function renameDisallowed(parsed, disallowedVars) {
    // rename all BOUND variables in parsed which are in disallowedVars to new variable names which are
    // all different to each other and the existing bound and free variables in parsed.
    //console.log(i, replacement, 'Disallowed:', disallowedVars);
    var renameMapping = new Map();
    for (const v of parsed.bound) {
        if (!disallowedVars.has(v)) continue;
        const vnew = getNewVarname(parsed, v[0], disallowedVars);
        renameMapping.set(v, vnew);
        parsed = parseSentence(replaceVariable(parsed.sentence, v, vnew));
    }
    return [parsed, renameMapping];
}
class ProverState {
    constructor() {
        this.axioms = AXIOMS.slice();
        this.definitions = new Set();
        this.statements = new Map();
        this.statementId = 0;
        this.operators = OPERATORS.slice();
        this.knownTheorems = new Map();
        this.actions = [];
        this.currentError = '';
        this.storage = undefined;
        this.mostRecentSave = 0;
        this.mostRecentTheorem = undefined;
        this.orcMap = new Map();
        this.filesImported = [];
        this.filesImportedManually = [];
        this.variableDefinitions = new Map();
        for (var [type, typename] of [[BASERELATIONS, 'RELATION'], [BASEOPERATORS, 'OPERATOR'], [BASECONNECTIVES, 'CONNECTIVE']])
            type.forEach((t, arity) => { t.forEach(rel => this.orcMap.set(rel, [typename, arity, undefined])); });
        this.AddRelation(2, '<=', 'Ex(((@1)+(x))=(@2))');
        this.AddRelation(2, '<', 'Ex(((@1)+(S(x)))=(@2))');
        this.AddRelation(2, '!<', '((@1)<(@2))=>(F)');
        this.AddRelation(2, '!=', '((@1)=(@2))=>(F)');
        this.AddRelation(2, '|', 'Ex(((@1)*(x))=(@2))');
        this.AddConnective(2, '||', '((P)=>(F))=>(Q)');
        this.AddConnective(2, '&&', '((P)=>((Q)=>(F)))=>(F)');
        this.AddRelation(3, '\'gcd', '(((@3)|(@1))&&((@3)|(@2)))&&(Ah((((h)|(@1))&&((h)|(@2)))=>((h)|(@3))))');
        this.AddRelation(3, '\'mod', '((@3)<(@2))&&(En((@1)=(((n)*(@2))+(@3))))');
        this.AddRelation(3, '\'cong', "Ea(('mod[@1,@3,a])&&('mod[@2,@3,a]))");
        this.AddRelation(3, '\'conga', "Ea(Eb(((@1)+((@3)*(a)))=((@2)+((@3)*(b)))))");
        this.AddRelation(2, '\'bezoutable', "((@1)!=(0))=>(((@2)!=(0))=>(Eu(Eg(('cong[(u)*(@1),g,@2])&&('gcd[@1,@2,g])))))");
        this.AddRelation(2, '\'br', "Ea(Eb(Eg(('gcd[@1,@2,g])&&(((a)*(@1))=(((b)*(@2))+(g))))))");
        this.AddRelation(2, '\'brr', "((@1)!=(0))=>('br[@1,@2])");
        this.AddRelation(1, '\'prime', "((S(0))<(@1))&&(Aa(((a)<(@1))=>(((a)|(@1))=>((a)=(S(0))))))");
        this.AddRelation(2, '\'nprod', "((@1)!=(0))&&(Ax(((x)<=(@2))=>(((x)!=(0))=>((x)|(@1)))))");
        for (var X of this.axioms) {
            var sentence = X[0];
            var parsed = parseSentence(sentence);
            if (!parsed.error) this.proveParsed(parsed, [], X[1], []);
            else this.currentError = renderParsed(parsed);
        }
        this.mostRecentTheorem = undefined; // don't count axioms
    }
    saveActions(force=false) {
        if ((!force) && Date.now() - this.mostRecentSave < 1000) return; // don't bother saving if you saved less than a second ago
        this.mostRecentSave = Date.now();
        if (this.storage) {
            //console.log('Saving...');
            localStorage.setItem(this.storage + 'Actions', JSON.stringify(this.actions, null, 1));
            localStorage.setItem(this.storage + 'FilesImportedManually', JSON.stringify(this.filesImportedManually, null, 1));
            //console.log('done!');
        }
    }
    recordAction(x) {
        this.actions.push(x);
        setTimeout(() => this.saveActions());
    }
    doAction(x) {
        try {
        return this[x[0]](...x[1]);
        } catch (e) {
            console.log('FAILED', x, e);
            return 0;
        }
    }
    importFiles(filenamesInitial, callback, loadProof=false) {
        if (loadProof && filenamesInitial.length != 1) {
            return callback([[],[]], 'If calling to load proof, must call with exactly one file');
        }
        if (filenamesInitial.length == 0) return callback([[], new Set()], undefined);
        const filenamesInitialSet = new Set(filenamesInitial);
        var filesToLoad = new Set();
        var self = this;
        var dataFromFilename = new Map(); // filenameInitial -> (contents, requirements that we don't already know, statements to export)
        var loadingFailedDueToLoop = false;
        var fullyVerifiedFiles = new Set();
        console.log('LOADING FILES...');
        filenamesInitial.forEach((f) => loadFileRecursive(f));

        // transitively puts all theorems into the above map
        function loadFileRecursive(filename, ancestors=[]) {
            //console.log('lfr', filename, ancestors);
            // first load the theorem, then for all its unloaded and unknown reqs, put them in the set
            // and call this recursively. If the map and the set are the same size we are done
            if (loadingFailedDueToLoop) return;
            if (ancestors.includes(filename)) {
                self.currentError = 'Loop detected in loadFileRecursive: ' + filename + ' is needed by chain ' + ancestors;
                loadingFailedDueToLoop = true;
                setTimeout(() => callback([false, false], self.currentError));
                return;
            }
            if (self.filesImported.includes(filename) && !filenamesInitialSet.has(filename)) return;
            if (filesToLoad.has(filename)) return;
            filesToLoad.add(filename);
            getFile('/PA_' + filename + '.js', function() {
                if (loadingFailedDueToLoop) return;
                const proof = window['proof_' + filename];
                const thmFromSentence = window['exportStatements_' + filename];
                const reqs = window['requiredModules_' + filename]; // required files
                
                for (const reqFile of reqs)
                    if (loadProof && filename == filenamesInitial[0])
                        filenamesInitialSet.add(reqFile);
                for (const reqFile of reqs) {
                    loadFileRecursive(reqFile, ancestors.concat([filename]));
                }
                dataFromFilename.set(filename, [proof, reqs, thmFromSentence]);
                if (dataFromFilename.size == filesToLoad.size) {
                    //console.log(dataFromFilename);
                    console.log('VERIFYING FILES...');
                    filenamesInitial.forEach(verifyFileRecursive);
                }
            });
        }

        function verifyFileRecursive(filename) {
            // skip if not needed because you already know the theorems
            if (self.filesImported.includes(filename) && !filenamesInitialSet.has(filename)) return true;
            if (fullyVerifiedFiles.has(filename)) return true;
            // FIRST recursively, and synchronously, prove all pre-requisites
            const [proof, reqs, thmFromSentence] = dataFromFilename.get(filename);
            for (const reqFile of reqs) {
                if (!verifyFileRecursive(reqFile)) return false;
            }
            //console.log('Loaded and verified prereqs, now proving', filename);
            var topLevelTheorems = []; // just names; only used if this is the "actual" file we want
            // THEN prove the actual theorem
            const useThis = (loadProof && filenamesInitial[0] == filename);
            var prover = useThis ? self : new ProverState();
            prover.knownTheorems = self.knownTheorems;
            //prover.orcMap = orcMap;
            for (const x of proof) {
                if (!prover.doAction(x)) {
                    console.log('Theorem verification FAILED:', x);
                    setTimeout(() => {callback([false, false], filename + ': ' + prover.currentError);});
                    return false;
                }
                if (thmFromSentence && thmFromSentence.has(prover.mostRecentTheorem))
                {
                    const thmName = thmFromSentence.get(prover.mostRecentTheorem);
                    self.knownTheorems.set(thmName, prover.mostRecentTheorem);
                    if (filenamesInitialSet.has(filename) && !topLevelTheorems.includes(thmName)) topLevelTheorems.push(thmName);
                }
            }
            //console.log('finished verifying "' + filename + '"');
            if (useThis) {
                setTimeout(()=>callback([[], filesToLoad], undefined));
                return true;
            }
            if (!thmFromSentence) {
                var sentence = prover.mostRecentTheorem;
                if (!sentence) {
                    console.log('verifiction FAILED, no last theorem!!!??', prover);
                    setTimeout(() => {callback([false, false], 'No most recent theorem');});
                    return false;
                };
                self.knownTheorems.set(filename, sentence);
                if (filenamesInitialSet.has(filename)) topLevelTheorems.push(filename);
            }
            self.filesImported.push(filename);
            if (filenamesInitialSet.has(filename)) self.filesImportedManually.push(filename);
            filenamesInitialSet.delete(filename);
            if (filenamesInitialSet.size == 0) setTimeout(()=> {callback([topLevelTheorems, filesToLoad], undefined);});
            fullyVerifiedFiles.add(filename);
            return true;
        }
    }
    SetComment(id, comment) {
        if (!this.statements.has(id)) return 0;
        var s = this.statements.get(id);
        s.comment = comment;
        this.recordAction(['SetComment', [id, comment], id, s.p.sentence]);
        return id;
    }
    Highlight(id) {
        if (!this.statements.has(id)) return 0;
        var s = this.statements.get(id);
        s.highlight = !s.highlight;
        this.recordAction(['Highlight', [id], id, s.p.sentence]);
        return id;
    }
    proveParsed(p, used, comment='', deps=[]) {
        if (p.error) {
            this.currentError = 'Failed to add: ' + renderParsed(p) + ' due to ' + p.error;
            return 0;
        }
        //if (someEntry(this.statements, (id,x) => x.p.sentence === p.sentence))
        //    this.currentError = 'Warning: already proved ' + renderParsed(p);
        this.statementId ++;
        deps = uniSort(deps);
        this.statements.set(this.statementId,
            {id: this.statementId, 'p': p, comment: comment, deps: deps, proved: true, highlight: false, used: used, deleted: false});
        if (deps.length == 0 && p.free.length == 0) {
            this.mostRecentTheorem = p.sentence;
            //console.log('New theorem:', this.mostRecentTheorem);
        }
        if (window.userOnProof)
            setTimeout(() => {window.userOnProof(this.statements.get(this.statementId));});
        return this.statementId;
    }
    assumeParsed(p) {
        this.statementId ++;
        this.statements.set(this.statementId,
            {id: this.statementId, 'p': p, comment: '', deps: [this.statementId], proved: false, highlight: false, used: [], deleted: false});
        return this.statementId;
    }
    Assume(sentence) {
        var success = 0;
        var parsed = parseSentence(sentence);
        if (parsed.error) {
            this.currentError = 'Failed to add: ' + renderParsed(parsed) + ' due to ' + parsed.error;
        //} else if (someEntry(this.statements, (id,x) => x.p.sentence === parsed.sentence)) {
        //    this.currentError = 'Already assuming ' + renderParsed(parsed);
        } else {
            var id = this.assumeParsed(parsed);
            this.recordAction(['Assume', [sentence], id, sentence]);
            success = id;
        }
        return success;
    }
    Quote(theoremName) {
        if (!this.knownTheorems.has(theoremName)) return 0;
        var sentence = this.knownTheorems.get(theoremName);
        var parsed = parseSentence(sentence);
        var success = this.proveParsed(parsed, [], theoremName, []);
        if (success) this.recordAction(['Quote', [theoremName], success, sentence]);
        return success;
    }
    Rewrite(id, claim) {
        if (!this.statements.has(id)) return 0;
        const s = this.statements.get(id);
        const parsedClaim = parseSentence(claim);
        if (parsedClaim.error) {
            this.currentError = "Invalid claim, due to " + parsedClaim.error;
            return 0;
        }
        if (!this.orcMap.has(parsedClaim.parsed[0])) {
            this.currentError = 'Must be a user-defined symbol: ' + parsedClaim.parsed[0];
            return 0;
        }
        const [typename, arity, defn] = this.orcMap.get(parsedClaim.parsed[0]);
        if (typename == 'RELATION') {
            const mapData = parsedClaim.parsed.slice(1).map((x,i) => ['@'+(i+1), x]);
            //console.log(mapData);
            const [expandedClaim, err] = this.rewriteSentence(parseSentence(defn, true), new Map(mapData));
            if (err) {
                this.currentError = err;
                return 0;
            }
            if (!isRenamingInstanceOf(expandedClaim, s.p)) {
                this.currentError = 'the following sentences are not equivalent: ' + expandedClaim.sentence + ' ' + s.p.sentence;
                return 0;
            }
            const parsed = parseSentence(claim);
            const success = this.proveParsed(parsed, [id], '', s.deps);
            if (success) this.recordAction(['Rewrite', [id, claim], success, parsed.sentence]);
            return success;
        } else if (typename == 'CONNECTIVE') {
            const pd = parseSentence(defn);
            const disallowedGenerics = new Set(pd.generics);
            var j = 0;
            while (disallowedGenerics.has('P'+j)) j++;
            const newGeneric = 'P' + j;
            const temp1 = replaceGeneric(defn, 'P', newGeneric);
            const temp2 = replaceGeneric(temp1, 'Q', parsedClaim.parsed[2].sentence);
            const temp3 = replaceGeneric(temp2, newGeneric, parsedClaim.parsed[1].sentence);
            const t3p = parseSentence(temp3);
            if (!isRenamingInstanceOf(t3p, s.p)) {
                this.currentError = 'the following sentences are not equivalent: ' + t3p.sentence + ' ' + s.p.sentence;
                return 0;
            }
            const parsed = parseSentence(claim);
            const success = this.proveParsed(parsed, [id], '', s.deps);
            if (success) this.recordAction(['Rewrite', [id, claim], success, parsed.sentence]);
            return success;
        } else return 0;
    }
    AddOperator(arity, symbol, sentence) {
        if (arity != 2) return 0;
        if (symbol.length > 2) return 0;
        if (this.orcMap.has(symbol)) {
            const [curType, curArity, curSentence] = this.orcMap.get(symbol);
            if (curType == 'OPERATOR' && curArity == 2 && curSentence == sentence) return -1; // success, we already knew it
            this.currentError = 'already have a different definition for ' + symbol;
            return 0;
        }
        // P be the "sentence"
        // f(a,b)=<term>
        // y=func(a,b) means (Ez. P[a,b,z] and y=z)
        // Q[func(a,b)] means (Ez. P[a,b,z] and Q[z])
        const parsed = parseTerm(sentence, true); // TODO
        if (parsed.error) {
            this.currentError = 'invalid formula ' + parsed.error;
            return 0;
        }
        if (parsed.free.length != 0 || !arrayEqual(parsed.generics, ['P','Q'])) {
            this.currentError = 'invalid formula, expect no free variables and only generics to be P and Q: ' + renderParsed(parsed);
            return 0;
        }
        this.orcMap.set(symbol, ['CONNECTIVE', 2, sentence]); // whatever, verify later lol
        CONNECTIVES[arity].push(symbol);
        this.recordAction(['AddConnective', [arity, symbol, sentence], -1, '']);
        return -1;
    }
    AddConnective(arity, symbol, sentence) {
        if (arity != 2) return 0;
        if (symbol.length > 2) return 0;
        if (this.orcMap.has(symbol)) {
            const [curType, curArity, curSentence] = this.orcMap.get(symbol);
            if (curType == 'CONNECTIVE' && curArity == 2 && curSentence == sentence) return -1; // success, we already knew it
            this.currentError = 'already have a different definition for ' + symbol;
            return 0;
        }
        const parsed = parseSentence(sentence);
        if (parsed.error) {
            this.currentError = 'invalid formula ' + parsed.error;
            return 0;
        }
        if (parsed.free.length != 0 || !arrayEqual(parsed.generics, ['P','Q'])) {
            this.currentError = 'invalid formula, expect no free variables and only generics to be P and Q: ' + renderParsed(parsed);
            return 0;
        }
        this.orcMap.set(symbol, ['CONNECTIVE', 2, sentence]); // whatever, verify later lol
        CONNECTIVES[arity].push(symbol);
        this.recordAction(['AddConnective', [arity, symbol, sentence], -1, '']);
        return -1;
    }
    AddRelation(arity, symbol, sentence) {
        if (arity < 1) return 0;
        if (symbol.length == 0) return 0;
        const prefix = symbol[0] == "'";
        if (!prefix) {
            if (arity != 2) {
                this.currentError = 'arity must be 2 for infix relations (those which don\'t start with "\'")';
                return 0;
            }
            if (symbol.length > 2) {
                this.currentError = 'infix symbol cannot be too long';
                return 0;
            }
        }
        if (prefix && /^'[a-z]*$/.test(symbol) == false) {
            this.currentError = 'symbol must be alphanumeric after apostrophe';
            return 0;
        }
        if (this.orcMap.has(symbol)) {
            const [curType, curArity, curSentence] = this.orcMap.get(symbol);
            if (curType == 'RELATION' && curArity == arity && curSentence == sentence) return -1; // success, we already knew it
            this.currentError = 'already have a different definition for ' + symbol + ' ' + curSentence + ' ' + sentence;
            return 0;
        }
        // requires that sentence either has exactly @1 (arity-1) or exactly @1 and @2 (arity-2) as free variables
        const parsed = parseSentence(sentence, true);
        if (parsed.error) {
            this.currentError = 'invalid formula ' + parsed.error;
            return 0;
        }
        if (!arrayEqual(uniSort(parsed.free), Array.from(Array(arity).keys()).map(i => '@'+(i+1)))) {
            this.currentError = 'invalid formula, want free variables to be @1 to @'+arity+': ' + renderParsed(parsed);
            return 0;
        }
        if (parsed.generics.length > 0) {
            this.currentError = 'invalid formula - cannot have generics: ' + renderParsed(parsed);
            return 0;
        }
        this.orcMap.set(symbol, ['RELATION', arity, sentence]);
        RELATIONS[arity].push(symbol);
        this.recordAction(['AddRelation', [arity, symbol, sentence], -1, '']);
        return -1;
    }
    // substitutions of type (variable string) => (parsed term)
    rewriteSentence(parsed, substitutions) { // given a permissive sentence, apply the substitutions, resolving conflicts.
        //console.log('Attempting rewrite', parsed, substitutions);
        const disallowed = new Set();
        for (var [i, x] of substitutions.entries()) if (!parseVariable(i, true)) return [undefined, 'FAILED rewrite, can only substitute variables'];
        for (var [i, x] of substitutions.entries()) for (var v of x.free) disallowed.add(v);
        //console.log(parsed.sentence, substitutions, disallowed);
        //if (parsed.free.some(f => disallowed.has(f))) return [undefined, 'FAILED rewrite, cannot rename free variables'];
        const [tempParsed, renameMapping] = renameDisallowed(parsed, disallowed);
        var temp = tempParsed.sentence;
        //console.log('renamed to avoid conflicts', temp);
        for (var [from, to] of substitutions.entries()){
            if (renameMapping.has(from)) from = renameMapping.get(from);
            temp = replaceVariable(temp, from, to.sentence);
        }
        //console.log('all subs done', temp);
        return [parseSentence(temp), undefined];
    }
    SubConnective(id, symbol, where) {
        if (!this.statements.has(id)) return 0;
        if (!this.orcMap.has(symbol)) {
            this.currentError = 'unknown symbol ' + symbol;
            return 0;
        }
        const [symbolType, symbolArity, symbolDefinition] = this.orcMap.get(symbol);
        if (symbolType != 'CONNECTIVE' || symbolArity != 2 || symbolDefinition == undefined) return 0;
        const s = this.statements.get(id);
        const P = s.p;
        if (!P.sentence.slice(where, where+symbol.length)==symbol) {
            this.currentError = 'cannot find symbol ' + symbol;
            return 0;
        }
        const t1end = where-1;
        const t1start = matchingBracketReverse(P.sentence, t1end);
        if (t1start == -1) {
            this.currentError = 'no matching bracket before the symbol';
            return 0;
        }
        const term1 = P.sentence.slice(t1start+1, t1end);
        const t1p = parseSentence(term1);
        if (t1p.error) {
            this.currentError = 'couldn\'t parse sentence ' + term1 + ' due to ' + t1p.error;
            return 0;
        }
        const t2start = where + symbol.length;
        const t2end = matchingBracket(P.sentence, t2start);
        if (t2end == -1) {
            this.currentError = 'no matching bracket after the symbol';
            return 0;
        }
        const term2 = P.sentence.slice(t2start+1, t2end);
        const t2p = parseSentence(term2);
        if (t2p.error) {
            this.currentError = 'couldn\'t parse sentence ' + term2 + ' due to ' + t2p.error;
            return 0;
        }
        const pd = parseSentence(symbolDefinition);
        const disallowedGenerics = new Set(pd.generics);
        var i = 0;
        while (disallowedGenerics.has('P'+i)) i++;
        const newGeneric = 'P' + i;
        const temp1 = replaceGeneric(symbolDefinition, 'P', newGeneric);
        const temp2 = replaceGeneric(temp1, 'Q', term2);
        const temp3 = replaceGeneric(temp2, newGeneric, term1);
        const parsedSubbed = parseSentence(temp3);
        if (parsedSubbed.error) {
            this.currentError = 'couldn\'t parse statement ' + parsedSubbed.sentence + ' due to ' + parsedSubbed.error;
            return 0;
        }
        const newSentence = P.sentence.slice(0, t1start) + parsedSubbed.sentence + P.sentence.slice(t2end+1);
        const parsed = parseSentence(newSentence);
        var success = this.proveParsed(parsed, [id], '', s.deps);
        if (success) this.recordAction(['SubConnective', [id, symbol, where], success, parsed.sentence]);
        return success;
    }
    SubRelation(id, symbol, where) {
        if (!this.statements.has(id)) return 0;
        if (!this.orcMap.has(symbol)) {
            this.currentError = 'unknown symbol ' + symbol;
            return 0;
        }
        const [relType, relArity, relDefinition] = this.orcMap.get(symbol);
        if (relType != 'RELATION' || relDefinition == undefined) return 0;
        const s = this.statements.get(id);
        const P = s.p;
        if (!P.sentence.slice(where, where+symbol.length)==symbol) {
            this.currentError = 'cannot find symbol ' + symbol;
            return 0;
        }
        if (symbol[0] == "'") {
            const j = P.sentence.indexOf(']', where);
            if (j == -1) {
                this.currentError=('could not find close bracket after relation ' + symbol + '; this should never happen???');
                console.log('aaaah', P.sentence, where);
                return 0;
            }
            const terms = P.sentence.slice(where+symbol.length+1, j).split(',');
            const parsedDefinition = parseSentence(relDefinition, true);
            const mapData = terms.map((t, i) => ['@'+(i+1), parseTerm(t)]);
            const [parsedSubbed, err] = this.rewriteSentence(parsedDefinition, new Map(mapData));
            if (err) {
                this.currentError = 'couldn\'t rewrite statement ' + parsedSubbed.sentence + ' due to ' + err;
                return 0;
            }
            if (parsedSubbed.error) {
                this.currentError = 'couldn\'t parse statement ' + parsedSubbed.sentence + ' due to ' + parsedSubbed.error;
                return 0;
            }
            const newSentence = P.sentence.slice(0, where) + parsedSubbed.sentence + P.sentence.slice(j+1);
            const parsed = parseSentence(newSentence);
            var success = this.proveParsed(parsed, [id], '', s.deps);
            if (success) this.recordAction(['SubRelation', [id, symbol, where], success, parsed.sentence]);
            return success;
        }
        const t1end = where-1;
        const t1start = matchingBracketReverse(P.sentence, t1end);
        if (t1start == -1) {
            this.currentError = 'no matching bracket before the symbol';
            return 0;
        }
        const term1 = P.sentence.slice(t1start+1, t1end);
        const t1p = parseTerm(term1);
        if (t1p.error) {
            this.currentError = 'couldn\'t parse term ' + term1 + ' due to ' + t1p.error;
            return 0;
        }
        const t2start = where + symbol.length;
        const t2end = matchingBracket(P.sentence, t2start);
        if (t2end == -1) {
            this.currentError = 'no matching bracket after the symbol';
            return 0;
        }
        const term2 = P.sentence.slice(t2start+1, t2end);
        const t2p = parseTerm(term2);
        if (t2p.error) {
            this.currentError = 'couldn\'t parse term ' + term2 + ' due to ' + t2p.error;
            return 0;
        }
        const parsedDefinition = parseSentence(relDefinition, true);
        const [parsedSubbed, err] = this.rewriteSentence(parsedDefinition, new Map([['@1', t1p], ['@2', t2p]]));
        if (err) {
            this.currentError = 'couldn\'t rewrite statement ' + parsedSubbed.sentence + ' due to ' + err;
            return 0;
        }
        if (parsedSubbed.error) {
            this.currentError = 'couldn\'t parse statement ' + parsedSubbed.sentence + ' due to ' + parsedSubbed.error;
            return 0;
        }
        const newSentence = P.sentence.slice(0, t1start) + parsedSubbed.sentence + P.sentence.slice(t2end+1);
        const parsed = parseSentence(newSentence);
        var success = this.proveParsed(parsed, [id], '', s.deps);
        if (success) this.recordAction(['SubRelation', [id, symbol, where], success, parsed.sentence]);
        return success;
    }
    asdfChangeBound(id, from, to) { // TODO decide if I keep this
        if (!this.statements.has(id)) return 0;
        var s = this.statements.get(id);
        if (!s.p.bound.includes(from)) {
            this.currentError = 'sentence ' + s.sentence + ' does not have ' + from + ' as a bound variable';
            return 0;
        }
        const parsed = parseSentence(replaceVariable(s.p.sentence, from, to));
        var success = this.proveParsed(parsed, [id], '', s.deps);
        if (success) this.recordAction(['ChangeBound', [id, from, to], success, parsed.sentence]);
        return success;
    }
    SV(id, replacement) {
        if (!this.statements.has(id)) return 0;
        var s = this.statements.get(id);
        var P = s.p;
        if (!(P.parsed[0] == 'A' || (P.parsed[0] == 'E' && replacement[0] == '#'))) return 0;
        var variable = P.parsed[1];
        var Q = P.parsed[2];
        var T = parseTerm(replacement);
        if (T.error) {
            this.currentError = 'could not parse variable ' + T.sentence + ' due to ' + T.error;
            return 0;
        }
        if (P.parsed[0] == 'E' && this.definitions.has(replacement)) {
            this.currentError = 'cannot define variable ' + replacement + ' as it is already defined';
            return 0;
        }
        const [newQ, renameMapping] = renameDisallowed(Q, new Set(T.free));
        //console.log('SV', newQ.sentence, Q.sentence);
        var newSentence = replaceVariable(newQ.sentence, variable, replacement);
        var parsed = parseSentence(newSentence);
        var success;
        if (P.parsed[0] == 'E') {
            const comment = 'Definition of <b>' + replacement + '</b>';
            success = this.proveParsed(parsed, [id], comment, s.deps);
            if (success) {
                this.variableDefinitions.set(replacement, success);
            }
        } else {
            success = this.proveParsed(parsed, [id], '', s.deps);
        }
        if (success) {
            this.recordAction(['SV', [id, replacement], success, parsed.sentence]);
            this.definitions.add(replacement);
        }
        return success;
    }
    DT(i1, i2) {
        if ((!this.statements.has(i1)) || (!this.statements.has(i2))) return 0;
        var s1 = this.statements.get(i1);
        var s2 = this.statements.get(i2);
        var sentence = '(' + s1.p.sentence + ')=>(' + s2.p.sentence + ')';
        var parsed = parseSentence(sentence);
        var newDeps = s2.deps.filter(x => x != s1.id);
        var success = this.proveParsed(parsed, [i1, i2], '', newDeps);
        if (success) this.recordAction(['DT', [i1, i2], success, parsed.sentence]);
        return success;
    }
    MP(i1, i2) {
        if ((!this.statements.has(i1)) || (!this.statements.has(i2))) {
            this.currentError = `one of ${i1}, ${i2} not existent`;
            return 0;
        }
        var s1 = this.statements.get(i1);
        var s2 = this.statements.get(i2);
        var p1 = s1.p;
        var p2 = s2.p;
        if (p1.parsed[0] == '=>' && p1.parsed[1].sentence == p2.sentence) {
            var parsed = parseSentence(p1.parsed[2].sentence);
            var success = this.proveParsed(parsed, [i1, i2], '', s1.deps.concat(s2.deps));
            if (success) this.recordAction(['MP', [i1, i2], success, parsed.sentence]);
            return success;
        }
        //this.currentError = 'MP failed: ' + renderParsed(p1) + ' and ' + renderParsed(p2);
        //console.log(p1, p2);
        // don't say anything because it tries both directions!
        return 0;
    }
    DEL(id) {
        if (!this.statements.has(id)) return 0;
        this.recordAction(['DEL', [id], id, this.statements.get(id).p.sentence]);
        this.statements.get(id).deleted = true;
        return id;
    }
    G(idx, variable) {
        if (!this.statements.has(idx)) return 0;
        if (variable[0] == '#') {
            this.currentError = 'Cannot generalize over definitional variable ' + variable;
            return 0;
        }
        var s = this.statements.get(idx);
        /*if (s.p.free.some(v=>v[0]=='#')) {
            this.currentError = 'Cannot generalize over a sentence that has a free definitional variable';
            return 0;
        }*/
        const deps = s.deps;
        const defDeps = s.p.free.flatMap(v => v[0]=='#'?this.variableDefinitions.get(v):[]);
        //console.log(defDeps);
        for (const id of s.deps.concat(defDeps)) {
            var s1 = this.statements.get(id);
            //if (s1.proved) continue;
            if (s1.p.free.includes(variable)) {
                this.currentError = 'The assumptions or definitions contain <b>' + variable + '</b> as a free variable, so this is invalid.';
                return 0;
            }
        }
        var sentence = `A${variable}(${s.p.sentence})`;
        var parsed = parseSentence(sentence);
        var success = this.proveParsed(parsed, [idx], '', s.deps);
        if (success) this.recordAction(['G', [idx, variable], success, parsed.sentence]);
        return success;
    }
    GE(idx, sentence) {
        if (!this.statements.has(idx)) return 0;

        const s = this.statements.get(idx);
        const sParsed = s.p;

        const claimParsed = parseSentence(sentence);
        if (claimParsed.error) {
            this.currentError = renderParsed(claimParsed);
            return 0;
        }
        if (claimParsed.parsed[0] != 'E') return 0;
        const variable = claimParsed.parsed[1];
        const subSentence = claimParsed.parsed[2].sentence; // should have `variable` only as free
        const j = searchToken(subSentence, variable);
        //console.log('search', subSentence, 'for', variable, 'at', j);
        var targetSentence = subSentence;
        if (j >= 0) { // at j is the first copy of what we want
            const replacement = getSubSentence(sParsed.sentence, j);
            const replacedSubSentence = replaceVariable(subSentence, variable, replacement);
            //console.log(replacement, replacedSubSentence);
            //console.log(sParsed.sentence, replacedSubSentence);
            targetSentence = replacedSubSentence;
        }
        if (sParsed.sentence != targetSentence) {
            this.currentError = 'Could not identify ' + renderParsed(sParsed) + ' as an example of ' + renderParsed(claimParsed);
            console.log('Error generalising to exists: want equal', sParsed.sentence, targetSentence);
            const replacement = getSubSentence(sParsed.sentence, j);
            console.log(subSentence, variable, replacement);
            return 0;
        }
        var success = this.proveParsed(claimParsed, [idx], '', s.deps);
        if (success) this.recordAction(['GE', [idx, sentence], success, claimParsed.sentence]);
        return success;
    }
    S(idx, gen, target) {
        if (!this.statements.has(idx)) return 0;
        var s = this.statements.get(idx);
        if (s.deps.length > 0) {
            this.currentError = 'can\'t specialise ' + gen + ' because that statement is, or depends on, unproven assumptions.';
            return 0;
        }
        var sentence = replaceGeneric(s.p.sentence, gen, target);
        const parsed = parseSentence(sentence);
        var success = this.proveParsed(parsed, [idx], '', s.deps);
        if (success) this.recordAction(['S', [idx, gen, target], success, parsed.sentence]);
        return success;
    }
    // if index is defined, get history of that statement; otherwise get history of all highlighted statements
    getHistory(index=undefined) {
        var oldIdsToKeep = new Set();
        const NUMAXIOMS = this.axioms.length;
        for (var i = 1; i <= NUMAXIOMS; ++ i) oldIdsToKeep.add(i);
        for (var ri = this.actions.length - 1; ri >= 0; ri --) {
            const record = this.actions[ri];
            if (record[0] == 'AddRelation' || record[0] == 'AddConnective' || record[0] == 'SetComment' && record[0] == 'Highlight' || record[0] == 'DEL') continue;
            const id = record[2];
            const s = this.statements.get(id);
            if ((!oldIdsToKeep.has(id)) && (s.id != index) && (index || !s.highlight)) continue;
            oldIdsToKeep.add(id);
            // add anything this statement used
            for (var idx of s.used) oldIdsToKeep.add(idx);
        }
        // "new" is off by NUMAXIOMS+1
        var newToOld = uniSort(oldIdsToKeep);
        var oldToNew = new Map();
        for (var i = 1; i < newToOld.length; ++ i) oldToNew.set(newToOld[i], i);
        var newActionsSoFar = [];
        var nextId = NUMAXIOMS+1;
        for (const oldRecord of this.actions) {
            if (!oldIdsToKeep.has(oldRecord[2])) continue;
            var newArgs = oldRecord[1];
            if (oldRecord[0] == 'DT' || oldRecord[0] == 'MP') newArgs = newArgs.map(a => (typeof a === "number" ? oldToNew.get(a)+1 : a));
            else newArgs[0] = (a => (typeof a === "number" ? oldToNew.get(a)+1 : a))(newArgs[0]);
            newActionsSoFar.push([
                oldRecord[0],
                newArgs,
                oldToNew.get(oldRecord[2])+1,
                oldRecord[3]]);
        }
        console.log(newActionsSoFar);
        return newActionsSoFar;
    }
}
var globalProver = new ProverState();
globalProver.storage = "globalProver_";
var modusPonensSelected = undefined;
var deductionTheoremSelected = undefined;
function assumptionFormSubmitted() {
    var sentence = document.getElementById('assumptionInput').value;
    if (window.userModifyInput)
        sentence = userModifyInput(sentence);
    if (sentence.length == 0) return;
    for (const s of sentence.split(', ')) {
        globalProver.Assume(s.trim());
    }
    updatePage();
}
function specialiseForall(s) {
    var P = s.p;
    var term = P.sentence[1];
    var replacement = prompt('replacement for ' + term + '?');
    if (!replacement) return;
    globalProver.SV(s.id, replacement);
    updatePage();
}
function specialiseExists(s) {
    var P = s.p;
    var term = P.sentence[1];
    var replacement = prompt('replacement for ' + term + '?');
    if (!replacement) return;
    if ((!parseVariable(replacement))) {
        globalProver.currentError = 'cannot parse definitional variable ' + replacement + ' (must be #, letter, alphanumeric)';
        updatePage();
        return;
    }
    if (replacement[0] != '#') replacement = '#' + replacement;
    globalProver.SV(s.id, replacement);
    updatePage();
}
function deductionTheorem(i) {
    if (deductionTheoremSelected === undefined) {
        deductionTheoremSelected = i;
        updatePage();
        return;
    }
    if (deductionTheoremSelected == i) {
        deductionTheoremSelected = undefined;
        updatePage();
        return;
    }
    globalProver.DT(deductionTheoremSelected, i);
    deductionTheoremSelected = undefined;
    updatePage();
}
function modusPonens(i) {
    if (modusPonensSelected === undefined) {
        modusPonensSelected = i;
        updatePage();
        return;
    }
    if (modusPonensSelected == i) {
        modusPonensSelected = undefined;
        updatePage();
        return;
    }
    if ((!globalProver.MP(modusPonensSelected, i)) && (!globalProver.MP(i, modusPonensSelected)))
        globalProver.currentError = "Modus ponens failed.";
    modusPonensSelected = undefined;
    updatePage();
}
function expandSymbol(i, symbol, where) {
    if (!globalProver.orcMap.has(symbol)) return;
    const typeName = globalProver.orcMap.get(symbol)[0];
    if (typeName == 'RELATION')
        globalProver.SubRelation(i, symbol, where);
    else if (typeName == 'CONNECTIVE')
        globalProver.SubConnective(i, symbol, where);
    updatePage();
}
function deleteStatement(i, check=false) {
    if (check && !confirm('Are you sure?')) return;
    globalProver.DEL(i);
    updatePage();
}
function commentStatement(i) {
    const comment = prompt('comment?');
    if (!comment) return;
    globalProver.SetComment(i, comment);
    updatePage();
}
function proverHighlight(i) {
    globalProver.Highlight(i);
    updatePage();
}
function generalizeStatement(s) {
    var x = prompt('Quantify over what variable?');
    if (!x) return;
    globalProver.G(s.id, x);
    updatePage();
}
function existentialiseStatement(i) {
    if (!globalProver.statements.has(i)) return;
    const s = globalProver.statements.get(i);
    var x = prompt('What do you want to deduce?');
    if (!x) return;
    globalProver.GE(s.id, x);
    updatePage();
}
function specStatement(i, generic=undefined) {
    const s = globalProver.statements.get(i);
    var parsed = s.p;
    generic = generic || prompt('What generic?');
    if (!generic) return;
    var P = prompt('Replace ' + generic + ' with what?');
    if (!P) return;
    globalProver.S(s.id, generic, P);
    updatePage();
}
function addRelation() {
    const rel = prompt("what arity-2 relation?");
    if (!rel) return;
    const defn = prompt ("what does @1"+rel+"@2 mean?");
    if (!defn) return;
    globalProver.AddRelation(2, rel, defn);
    updatePage();
}
function addConnective() {
    const rel = prompt("what arity-2 connective?");
    if (!rel) return;
    const defn = prompt ("what does P"+rel+"Q mean?");
    if (!defn) return;
    globalProver.AddConnective(2, rel, defn);
    updatePage();
}
function copyStatement(i) {
    navigator.clipboard.writeText(globalProver.statements.get(i).p.sentence);
}
function rewriteStatement(i) {
    var claim = prompt("Rewrite with a symbol");
    if (!claim) return;
    globalProver.Rewrite(i, claim);
    updatePage();
}
function updatePage() {
    var output = '';
    for (const [i, statement] of globalProver.statements.entries()) {
        if (statement.deleted) continue;
        var style = statement.highlight ? 'background-color:white' : '';
        output += "<tr style='"+style+"' id='statement"+i+"'><td>"+i+"</td><td style='white-space: nowrap; width: 1px; padding-right: 5px'>" +
    //    "<button onclick='saveStatement("+i+")'>&#128190;</button>" +
        "<button title='Copy the underlying statement' onclick='copyStatement("+i+")'>&#9986;</button>" +
        "<button title='Quantify over all of some variable' onclick='generalizeStatement(globalProver.statements.get("+i+"))'>&forall;</button>" +
        "<button title='Quantify over one of some variable' onclick='existentialiseStatement("+i+")'>&exist;</button>" +
        "<button title='Use this as one of two statements in modus ponens' onclick='modusPonens("+i+")'>&rArr;</button>" +
        "<button title='Use this statement in a deduction' onclick='deductionTheorem("+i+")'>D</button>" +
        "<button title='Rewrite this statement to use a predefined operator' style='height:22px' onclick='rewriteStatement("+i+")'>&#9998;</button>" +
        "<button title='Add a comment' onclick='commentStatement("+i+")'>c</button>"+
        "<button title='Highlight' onclick='proverHighlight("+i+")'>#</button>"+
        "<button title='Delete' onclick='deleteStatement(" + (i) + ",true)' >x</button>"+
        "</td><td style='width:50%'>" + renderClickable(statement) + "</td><td>" + statement.comment + "</td><td>" + statement.deps + "</td></tr>";
    }
    //var scrollpos = window.scrollY;
    document.getElementById("statementTable").innerHTML = output;
    //if (scrollpos) window.scrollTo(0, scrollpos);
    document.getElementById('errorLogging').innerHTML = globalProver.currentError;
    if (modusPonensSelected >= 0)
        document.getElementById("statement"+modusPonensSelected).style['background-color'] = '#ccffcc';
    if (deductionTheoremSelected >= 0)
        document.getElementById("statement"+deductionTheoremSelected).style['background-color'] = '#aaccff';
    globalProver.currentError = '';
}
function completeReset() {
    if (!confirm("Are you sure you want to reset?")) return;
    globalProver.actions = [];
    globalProver.filesImported = [];
    globalProver.filesImportedManually = [];
    globalProver.saveActions();
    window.location.reload();
}
function saveModule() {
    var stateName = prompt('Name to save module under?');
    if (!stateName) return;
    if (globalProver.filesImported.includes(stateName)) {
        alert('cannot save with name ' + stateName + ' as you imported a file with this name already');
        return;
    }
    const history = globalProver.actions;
    var toExport = new Map();
    for (const [id, s] of globalProver.statements.entries()) {
        if (id > AXIOMS.length && s.highlight && s.comment.length > 0 && !s.deleted)
            toExport.set(s.p.sentence, s.comment);
    }
    var fileContents = escape('window.exportStatements_' + stateName + ' = new Map(' + JSON.stringify([...toExport.entries()]) + ');\n\n' +
    'window.requiredModules_' + stateName + ' = ' + JSON.stringify(globalProver.filesImportedManually) + ';\n\n' +
        'window.proof_' + stateName + ' = ' + JSON.stringify(history, null, 1) + ';');
    var link = document.createElement('a');
    link.download = 'PA_' + stateName + '.js';
    link.href = 'data:,' + fileContents;
    link.click();
}
function saveStatement(i) {
    if (!globalProver.statements.has(i)) return;
    var s = globalProver.statements.get(i);
    if (s.deps.length || s.p.free.length) {
        globalProver.currentError = 'can\'t save a non-theorem (this statement has assumptions) or free variables';
        updatePage();
        return;
    }
    var theoremName = prompt('Name to save theorem under?');
    if (!theoremName) return;
    const history = globalProver.getHistory(i);
    var fileContents = escape('window.requiredModules_' + theoremName + ' = ' + JSON.stringify(globalProver.filesImportedManually) + ';\n\n' +
        'window.proof_' + theoremName + ' = ' + JSON.stringify(history, null, 1) + ';');
    var link = document.createElement('a');
    link.download = 'PA_' + theoremName + '.js';
    link.href = 'data:,' + fileContents;
    link.click();
    globalProver.knownTheorems.set(theoremName, s.p.sentence);
}
function doFilterHistory () {
    var newActionsSoFar = globalProver.getHistory();
    globalProver.actions = newActionsSoFar;
    globalProver.saveActions();
    window.location.reload();
}
// filenameInitial is a string; knownTheorems maps from thm name to sentence; callback takes `proved` map and error.
// loadProof will show the proof on the page, not just the exported results.
// knownTheorems will be edited in place.
function importFile(filename=undefined, callback=undefined) {
    filename = filename || prompt('What theorem to import?');
    if (!filename) return;
    globalProver.importFiles([filename], function([theorems, allFiles], error) {
        if (error) {
            alert(error);
            console.log(error);
            console.log(globalProver.currentError);
            updatePage();
            return;
        }
        console.log('succeeded importing:', theorems, allFiles);
        for (const theorem of theorems) globalProver.Quote(theorem);
        updatePage();
        callback && callback();
    });
}
function inspectFile() {
    const filename = prompt('What file to open? WARNING: will lose progress');
    if (!filename) return;
    globalProver.importFiles([filename], function([theorems, allFiles], error) {
        if (error) {
            alert(error);
            console.log(error);
            console.log(globalProver.currentError);
            updatePage();
            return;
        }
        //console.log('succeeded importing:', theorems, allFiles);
        updatePage();
    }, true);
}
function getFile(path, callback) {
    var scr = document.createElement('script');
    scr.src = '/prover/'+path;
    scr.onload = callback;
    document.head.appendChild(scr);
}
function showMessage(title, message) {
    document.getElementById('popup-header').innerHTML = '&#x1F3B9;&nbsp;&nbsp;' + title;
    document.getElementById('popup-body').innerHTML = message;
    document.getElementById('bodyDisable').style.display = 'initial';
    document.getElementById('popup').style.display = 'initial';
}
function hideMessage() {
    document.getElementById('bodyDisable').style.display = 'none';
    document.getElementById('popup').style.display = 'none';
}
function keyPressEvent(e) {
    e = e || window.event;
    if (e.key == "Escape") {
        hideMessage();
    }
}
function showExplanation() {
    showMessage("What is this?", `<h4>Intro</h4>This is a theorem verifier for Peano arithmetic. There are a few added features to make life easier, but all the theorems you can prove are provable by Peano arithmetic.<br>
    Peano arithmetic is a system for proving statements about the natural numbers, which are the numbers 0, 1, 2, and so on. We can say (and prove) things like "for all x there is a prime number bigger than x".<br>
    <h4>Symbols</h4>The way we write statements in Peano arithmetic might look unfamiliar. However, if you read the symbols out loud to yourself it should resemble an English sentence.
    <ul><li>&forall; reads as "for all", and goes before a variable to introduce that variable for later use. &forall;x (blah) means "for all x (in the natural numbers), blah is true". blah can be any statement about x or other variables. Here's an obvious one: &forall;x (x=x).</li>
    <li>S is the successor function, so S(x) is the number after x, i.e. x+1. Why do we bother with this when we can just write x+1? Well, since 1 is really S(0), we actually can't write 1 at all without S. So we either introduce a "1" symbol or an "S" symbol, and Peano chose S.
    <li>&rArr; reads as "implies", or you can read P&rArr;Q as "if P then Q". For example, (x=y)&rArr;(S(x)=S(y)) can be read as "if x equals y then S(x) equals S(y)", or even as "if x equals y then x+1 equals y+1".</li>
    <li>&bot; reads as "false", and we usually use it in a statement like P&rArr;&bot;, which says "P implies false", or in other words "if P is true then false is true", or in <i>other</i> other words, "P is false".</li>
    <li>P, Q, R: these are placeholders for any statement; click on them to replace them with a statement of your choice.</li>
    </ul>
    <h4>Axioms</h4>
    Let's go through the axioms and make sense of them. <br>
    A1. <b>P&rArr;(Q&rArr;P)</b>. If P is true, then (if Q is true, P is true). I.e., if P is true, then anything implies it.<br>
    A2. <b>(P&rArr;(Q&rArr;R))&rArr;((P&rArr;Q)&rArr;(P&rArr;R))</b>. If P implies that Q implies R, and if P also implies Q, then P must imply R. In other words, in the presence of P, if Q is true and Q implies R then R is true.<br>
    A3. ${renderSentence('(((P)=>(F))=>(F))=>(P)')}. If it is not true that P is false, then P is true. This is the 'law of the excluded middle': it says there is no middle ground between true and false.<br>
    A4. ${renderSentence(AXIOMS[3][0])}. For all x, x equals itself.<br>
    A5. ${renderSentence(AXIOMS[4][0])}. For all x and for all y, if they are equal then any proposition about x is also true about y.<br>
    A6. ${renderSentence(AXIOMS[5][0])}. For all x, if a proposition P is true about every y, then it is true about x.<br>
    A7. ${renderSentence(AXIOMS[6][0])}. If for every x P implies Q, and x doesn't appear in P, then you can move the forall sign to the right.<br>
    PA1. ${renderSentence(AXIOMS[7][0])}. For all x and y, if S(x)=S(y) then x=y. I.e., S can't take two different values to the same value. This makes sense, as we know that you can't add 1 to two different numbers and get the same result.<br>
    PA2. ${renderSentence(AXIOMS[8][0])}. For all x, it is not true that S(x)=0, i.e. for all x, S(x) is not 0. Remember we are only talking about whole numbers from 0 upwards here, so none of them is -1.<br>
    PA3. ${renderSentence(AXIOMS[9][0])}. For any x, if we add 0 to x we just get x.<br>
    PA4. ${renderSentence(AXIOMS[10][0])}. For any x and y, x+(y+1)=(x+y)+1.<br>
    PA5. ${renderSentence(AXIOMS[11][0])}. For any x, x times 0 is 0.<br>
    PA6. ${renderSentence(AXIOMS[12][0])}. For any x and y, x(y+1)=xy+x.<br>
    PA7. ${renderSentence(AXIOMS[13][0])}. If some proposition P is true of 0, and whenever it is true of x it is true of x+1, then it is true of all x. This is the famous axiom of induction.
    <h4>Basic features</h4>
    <b>Specialisation.</b> To specialise a statement that starts with a &forall; symbol, click the symbol and type in the expression you want to replace it with. If you do this for A4 and type in 0, you get 0=0. If you type in y, you see y=y.<br>
    <b>Generalisation.</b> We can also do the reverse: given the statement y=y, we can conclude that &forall;y (y=y). This is called generalisation, and you can do it by clicking the button that has a &forall; symbol and typing the name of the variable you want to quantify over. In this case we can quantify over y to get &forall;y (y=y), or we could even quantify over something else like z to get &forall;z (y=y).<br>
    <b>Modus Ponens.</b> If we have two sentences written down where one is of the form P&rArr;Q and the other is just P, then we can conclude Q. Do this by clicking the &rArr; button for the P&rArr;Q and P sentences.<br>
    <b>Specialisation of a generic proposition.</b> Generic propositions like P, Q and R can be replaced with any proposition by clicking on them and typing a replacement. This will not work if the sentence with the generic proposition depends on any assumptions, though.<br>
    Some generic propositions take arguments, as you can see in the last axiom. We might want P[0] to say something about 0, and P[x] to say something about x. To do this, click on the generic proposition and type in the sentence you want, but using '@' to denote places to put in the argument (e.g. 0 or x respectively).<br>
    <h4>And one more thing.</h4>
    The above is technically enough to prove everything Peano arithmetic can prove, but there is one simple thing that makes life a lot easier, which is the D button. To use it, first "assume" a statement (by typing it in the command box at the bottom) and then use the statement to deduce whatever result you want (using the above methods). The results you derive from this assumption will depend on the assumption via a number on the right hand side. These numbers show what dependencies a statement has in terms of its assumptions.<br>
    Once you have started with some assumption P and used it to deduce Q, it would make sense to conclude P&rArr;Q. This is what the D button does: just press the button on the P sentence and then on the Q sentence, and you'll get P&rArr;Q. If you look at the assumptions on the right, the number refering to the P assumption should not be there.
    <h4>And that's it! Kind of.</h4>
    This is technically enough to prove everything that Peano arithmetic can prove, but the proofs can be quite tedious, so there are extra 'advanced' features to make life a bit easier. Click on the advanced features button to get an overview, or try some of the examples to get started.`);
}
function showExample1() {
    showMessage("Example 1: (P=>Q)=>((Q=>R)=>(P=>R))", "<ol><li>Assume P=>Q (type <code>(P)=>(Q)</code> into the command box). It should appear at the bottom of the table, highlighted in red to show that it is an assumption.</li><li>Assume Q=>R (type <code>(Q)=>(R)</code> into the command box)</li><li>Now we want to prove P=>Q, so assume P</li><li>Combine the rows P and P=>Q to get Q (do this by clicking the => symbol on both rows)</li><li>Similarly for Q and Q=>R</li><li>Now from 'assuming' P we have 'deduced' R, so combine them to conclude P=>R (do this by clicking the D symbol on P, then on R)</li><li>Similarly click the D symbol on Q=>R and then P=>R</li><li>Do one more deduction to finish</li><li>You should have the target theorem in the last line of the proof. If you look on the right hand side, you can see which assumptions each statement depends on; the statement 'R' should depend on all three assumptions because you used all three to conclude it.</li></ol>");
}
function showExample2() {
    showMessage(`Example 2: &forall;x (x=0)?`, `<ol>
<li>Assume x=0 (type (x)=(0) in the command box).</li>
<li>Quantify over x because we are feeling naughty. (Press the &forall; button and enter x when asked what to quantify over).</li>
<li>This doesn't work because we assumed something about x, so we can't conclude that the statement is true for all x.</li>
<li>Quantify over y (press the same button but enter y).</li>
<li>Does the result seem reasonable?</li>
<li>We can discharge our assumption by using the "deduce" button (with a D on it). Press the D button for the initial assumption and then for the conclusion &forall;y (x=0)</li>
<li>Now this statement doesn't depend on any assumptions: there should be no numbers to the right showing that it depends on anything. So we can quantify over any variable, even x. Does this give us a sensible statement?</li>
    </ol>`);
}
function bodyOnLoad() {
    document.onkeydown = keyPressEvent;
    const files = JSON.parse(localStorage.getItem("globalProver_FilesImportedManually"));
    const actions = JSON.parse(localStorage.getItem("globalProver_Actions"));
    //console.log('files and actions:', files, actions);
    if (files) {
        globalProver.importFiles(files, (data, error) => {
            if (error) {
                alert('FAILED TO LOAD FILES:', error);
                console.log(globalProver.currentError);
                updatePage();
                if (window.userOnLoad) setTimeout(() => { window.userOnLoad(); });
                return;
            }
            doneLoadingFiles();
        });
    } else doneLoadingFiles();
    function doneLoadingFiles() {
        if (!actions) {
            updatePage();
            if (window.userOnLoad) setTimeout(() => { window.userOnLoad(); });
            return;
        }
        for (var i = 0; i < actions.length; ++ i) {
            const x = actions[i];
            if (!globalProver.doAction(x)) {
                alert('FAILED TO LOAD at ' + i + ' of ' + actions.length);
                console.log('FAILED TO LOAD', i, x, actions, globalProver.currentError);
                updatePage();
                return false;
            }
        };
        globalProver.saveActions(true);
        updatePage();
        if (window.userOnLoad) setTimeout(() => { window.userOnLoad(); });
    }
}
