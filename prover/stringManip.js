function isRenamingInstanceOf(parsed1, parsed2, mustRename=new Map()) {
    // can you rename bound variables of p1 to get p2? (easier version of "substitution instance").
    // also, anything in mustRename must be renamed to what it says, even free variables.
    if (parsed1.error || parsed2.error) return false;
    const p1 = parsed1.parsed, p2 = parsed2.parsed;
    if (parseVariable(p1[0]) && parseVariable(p2[0])) {
        if (mustRename.has(p1[0])) return p2[0] == mustRename.get(p1[0]);
        return p2[0] == p1[0];
    }
    if (p1[0] != p2[0]) {
        return false;
    }
    if (RELATIONS[2].includes(p1[0]) || CONNECTIVES[2].includes(p1[0]) || OPERATORS[2].includes(p1[0])) {
        return isRenamingInstanceOf(p1[1], p2[1], mustRename) && isRenamingInstanceOf(p1[2], p2[2], mustRename);
    } else if (OPERATORS[1].includes(p1[0])) {
        return isRenamingInstanceOf(p1[1], p2[1], mustRename);
    } else if (OPERATORS[1].includes(p1[0])) {
        return true;
    } else if (isGeneric(p1[0])) {
        const subs1 = p1.slice(1), subs2 = p2.slice(2);
        return subs1.length == subs2.length && subs1.every((x, i) => (isRenamingInstanceOf(x, subs2[i], mustRename)));
    } else if (p1[0] == 'A' || p1[0] == 'E') {
        const newMustRename = new Map(mustRename);
        newMustRename.set(p1[1], p2[1]);
        return isRenamingInstanceOf(p1[2], p2[2], newMustRename);
    } else if (p1[0] == 'F') {
        return true;
    } else if (p1[0] == '0') {
        return true;
    } else if (p1[0][0] == "'") {
        if (p1[0] != p2[0]) return false;
        if (p1.length != p2.length) throw new Error('same operator, different arities????');
        for (var i = 1; i < p1.length; ++ i) {
            if (!isRenamingInstanceOf(p1[i], p2[i], mustRename)) return false;
        }
        return true;
    } else {
        alert('errrrrr'+p1[0]);
        throw new Error('should never happen: isRenamingInstanceOf called on invalid strings');
    }
}
function replaceGeneric(sentenceOrig, gen, replaceOrig) {
    const rop = parseSentence(replaceOrig);
    const sop = parseSentence(sentenceOrig);
    const [sentenceParsed, renaming1] = renameDisallowed(sop, new Set(rop.free.concat(rop.bound)));
    var sentence = sentenceParsed.sentence;
    const [replaceParsed, renaming2] = renameDisallowed(rop, new Set(sentenceParsed.free));
    const replace = replaceParsed.sentence;
    // replacement contains @, @1, @2 etc symbols for the replacements, if any
    for (var i = 0; i < sentence.length; ++ i) {
        if (sentence.slice(i, i + gen.length) != gen) continue;
        if (i+gen.length >= sentence.length) throw new Error('generic without following brackets');
        if (sentence[i+gen.length] == ')') {
            sentence = sentence.slice(0, i) + replace + sentence.slice(i+gen.length);
            i += replace.length;
            continue;
        }
        if (sentence[i+gen.length] != '[') throw new Error('no open square bracket!!!');
        var j = sentence.indexOf(']', i);
        if (j == -1) throw new Error('no close square bracket!!!');
        var terms = sentence.slice(i+gen.length+1, j).split(',');
        var replacement = replace;
        for (var k = 0; k < terms.length; ++ k) replacement = replaceVariable(replacement, '@'+(k+1), terms[k]);
        replacement = replaceVariable(replacement, '@', terms[0]);
        sentence = sentence.slice(0, i) + replacement + sentence.slice(j+1);
        i += replacement.length;
    }
    return sentence;
}
function replaceVariable(sentence, find, replace) {
    return sentence
        .replaceAll('('+find+')', '('+replace+')')
        .replaceAll('['+find+']', '['+replace+']')
        .replaceAll(','+find+']', ','+replace+']')
        .replaceAll(','+find+',', ','+replace+',')
        .replaceAll('['+find+',', '['+replace+',')
        .replaceAll('A'+find+'(', 'A'+replace+'(')
        .replaceAll('E'+find+'(', 'E'+replace+'(');

}
function getSubSentence(sentence, start) {
    var depth = 0;
    for (var i = start; i < sentence.length; ++ i) {
        if (sentence[i] == '(' || sentence[i] == '[') depth ++;
        if (sentence[i] == ')' || sentence[i] == ']') depth --;
        if (depth == 0 && sentence[i] == ',') break;
        if (depth == -1) break;
    }
    return sentence.slice(start, i);
}
function searchToken(sentence, tok, start=0) {
    for (var i = start; i < sentence.length; ++ i) {
        if (sentence[i] == "'") {
            i ++;
            while (i < sentence.length && sentence[i] >= 'a' && sentence[i] <= 'z') ++ i;
            continue;
        }
        if (sentence[i] == '#' && sentence.slice(i, i+tok.length) === tok) return i;
        if (sentence[i] == '#') {
            i++; continue;
        }
        if (sentence.slice(i, i+tok.length) === tok && !(sentence[i+tok.length+1] >= '0' && sentence[i+tok.length+1] <= '9'))
            return i;
    }
    return -1;
}
