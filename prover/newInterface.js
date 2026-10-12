(function () {
class HelperState {
    constructor(prover) {
        this.prover = prover;
        this.currentError = undefined;
        this.wantedReverse = [];
        this.prettyPrintedTokens = [];
        this.endedEarly = false;
    }
    readTokens(toks) {
        const endPoint = toks.indexOf('?');
        toks = toks.slice(0, endPoint==-1 ? toks.length : endPoint);
        this.endedEarly = endPoint != -1;
        for (var i = 0; i < toks.length; ++ i) {
            const tok = toks[i];
            if (tok.startsWith('//')) {
                this.prettyPrintedTokens.push('<span style="font-family:serif;color:gray;font-weight:bold">'+tok.replaceAll('<', '&lt;')+'</span>');
            } else if (tok.startsWith('/*')) {
                this.prettyPrintedTokens.push('<span style="font-family:serif;color:gray;font-weight:bold">'+tok.replaceAll('\n', '<br>')+'</span>');
            } else if (tok == '\n') {
                if (this.prettyPrintedTokens.length > 0 && this.prettyPrintedTokens[this.prettyPrintedTokens.length-1] != '<br>')
                    this.prettyPrintedTokens.push('<br>');
            } else if (tok == 'done') {
                this.prettyPrintedTokens.push('<span style="color:blue;font-weight:bold">'+tok+'</span>');
                const [assumptions, want, then] = this.wantedReverse[this.wantedReverse.length-1];
                const parsed = parseSentence(want);
                if (parsed.error) {
                    alert('impossible: previously vetted sentence is invalid: ' + want);
                    return;
                }
                if (!assumptions.includes(want)) {
                    this.prettyPrintedTokens.push('Error, you are only done if you are assuming what you want to prove');
                    return;
                }
            } else if (tok == 'want') {
                this.prettyPrintedTokens.push('<span style="color:blue;font-weight:bold">'+tok+'</span>');
                i++;
                if (i >= toks.length) return;
                const parsed = parseSentence(toks[i]);
                if (parsed.error) {
                    this.prettyPrintedTokens.push(renderParsed(parsed) + ' ' + parsed.error);
                    return;
                }
                const rendered = renderParsed(parsed);
                this.prettyPrintedTokens.push(rendered);
                var currentAssumptions = [];
                if (this.wantedReverse.length)
                    currentAssumptions = this.wantedReverse[this.wantedReverse.length-1][0];
                this.wantedReverse.push([currentAssumptions.slice(), toks[i], []]);
            } else if (tok == 'suff') {
                this.prettyPrintedTokens.push('<span style="color:blue;font-weight:bold">'+tok+'</span>');
                i++;
                if (i >= toks.length) return;
                const [assumptions, want, then] = this.wantedReverse[this.wantedReverse.length-1];
                const parsed = parseSentence(want);
                if (parsed.error) {
                    alert('impossible: previously vetted sentence is invalid: ' + want);
                    return;
                }
                if (toks[i] == 'direct') {
                    this.prettyPrintedTokens.push(toks[i]);
                    if (want[0] == 'A') {
                        this.wantedReverse.push([assumptions.slice(), parsed.parsed[2].sentence, [['G', 'wanted', parsed.parsed[1], 'wanted']]]);
                    } else if (parsed.parsed[0] == '=>') {
                        this.wantedReverse.push([assumptions.concat(parsed.parsed[1].sentence), parsed.parsed[2].sentence, [['DT', parsed.parsed[1].sentence, parsed.parsed[2].sentence]]]);
                    } else {
                        this.prettyPrintedTokens.push('<br><span style="color:red">Can only directly prove stuff with a forall or implies</span>');
                        return;
                    }
                } else if (toks[i] == 'indirect') {
                    this.prettyPrintedTokens.push(toks[i]);
                    const lastAssumption = assumptions[assumptions.length-1];
                    const newSentence = '(' + lastAssumption + ')=>(' + want + ')';
                    this.wantedReverse.push([assumptions.slice(0, assumptions.length-1), newSentence, []]);
                } else if (toks[i] == 'cv') {
                    this.prettyPrintedTokens.push(toks[i]);
                    i++;
                    if (i >= toks.length) return;
                    if (!parseVariable(toks[i])) {
                        this.prettyPrintedTokens.push('<b style="color:red">Invalid replacement '+toks[i]+'</b>');
                        return;
                    }
                    this.prettyPrintedTokens.push(toks[i]);
                    const newSentence = this.prover.rewriteSentence(parseSentence(want), new Map([[parsed.parsed[1], parseTerm(toks[i])]]))[0].sentence;
                    this.wantedReverse.push([assumptions.slice(), newSentence, [['SV', 'wanted', parsed.parsed[1], 'specialised'], ['G', 'specialised', parsed.parsed[1], 'wanted']]]);
                } else if (toks[i] == 'induct') {
                    this.prettyPrintedTokens.push(toks[i]);
                    if (want[0] != 'A') {
                        this.prettyPrintedTokens.push('<br><span style="color:red">Can only inductively prove stuff with a forall predicate</span>');
                        return;
                    }
                    const inductionBit = 'Ax((' + parsed.parsed[2].sentence + ')=>(' + replaceVariable(parsed.parsed[2].sentence, parsed.parsed[1], 'S('+parsed.parsed[1]+')') + '))';
                    this.wantedReverse.push([assumptions.slice(), inductionBit, []]);
                    this.wantedReverse.push([assumptions.slice(), replaceVariable(parsed.parsed[2].sentence, parsed.parsed[1], '0'), []]);
                } else if (toks[i] == 'or') {
                    this.prettyPrintedTokens.push(toks[i]);
                    if (parsed.parsed[0] != '||') {
                        this.prettyPrintedTokens.push('error, should be trying to prove an or statement');
                        return;
                    }
                    i++;
                    if (i >= toks.length) return;
                    if (toks[i] == 'rhs') {
                        this.prettyPrintedTokens.push(toks[i]);
                        this.wantedReverse.push([assumptions.slice(), parsed.parsed[2].sentence, []]);
                    } else {
                        this.prettyPrintedTokens.push(toks[i]);
                        this.prettyPrintedTokens.push('error, expected rhs');
                    }
                } else {
                    this.prettyPrintedTokens.push('<b style="color:red">'+toks[i]+'</b>');
                    return;
                }
            } else if (tok == 'case') {
                this.prettyPrintedTokens.push('<span style="color:blue;font-weight:bold">'+tok+'</span>');
                i++;
                if (i >= toks.length) return;
                const [assumptions, want, then] = this.wantedReverse[this.wantedReverse.length-1];
                const parsed = parseSentence(want);
                if (parsed.error) {
                    alert('impossible: previously vetted sentence is invalid: ' + want);
                    return;
                }
                const caseParsed = parseSentence(toks[i]);
                if (caseParsed.error) {
                    this.prettyPrintedTokens.push(renderParsed(caseParsed) + ' ' + caseParsed.error);
                    return;
                }
                if (caseParsed.parsed[0] != '||') {
                    this.prettyPrintedTokens.push('<br><span style="color:red">Expect an "or" statement</span>');
                    return;
                }
                const rendered = renderParsed(caseParsed);
                this.prettyPrintedTokens.push(rendered);
                const s1 = '(' + caseParsed.parsed[1].sentence+')=>('+want+')';
                const s2 = '(' + caseParsed.parsed[2].sentence+')=>('+want+')';
                const p1 = parseSentence(s1);
                const p2 = parseSentence(s2);
                if (p1.error) {
                    this.prettyPrintedTokens.push('<br>ERROR in sentence ' + renderParsed(p1) + ': ' + p1.error);
                    return;
                }
                if (p2.error) {
                    this.prettyPrintedTokens.push('<br>ERROR in sentence ' + renderParsed(p2) + ': ' + p2.error);
                    return;
                }
                this.wantedReverse.push([assumptions.slice(), '('+caseParsed.parsed[1].sentence+')=>('+want+')', []]);
                this.wantedReverse.push([assumptions.slice(), '('+caseParsed.parsed[2].sentence+')=>('+want+')', []]);
                this.wantedReverse.push([assumptions.slice(), toks[i], []]);
            } else if (tok == 'quote') {
                this.prettyPrintedTokens.push('<span style="color:blue;font-weight:bold">'+tok+'</span>');
                i++;
                if (i >= toks.length) return;
                const theoremName = toks[i];
                if (!this.prover.knownTheorems.has(theoremName)) {
                    this.prettyPrintedTokens.push(theoremName);
                    this.prettyPrintedTokens.push('<b style="color:red">unknown theorem</b>');
                    return;
                }
                this.prettyPrintedTokens.push('<b style="color:green">'+theoremName+'</b>');
                this.wantedReverse[this.wantedReverse.length-1][0].push(this.prover.knownTheorems.get(theoremName));
            } else if (tok == 'skip') {
                this.prettyPrintedTokens.push('<span style="color:blue;font-weight:bold">'+tok+'</span>');
                this.wantedReverse.pop();
            } else if (tok == '<ERROR>') {
                this.prettyPrintedTokens.push('<b style="color:red">ERROR</b>');
                return;
            } else {
                this.prettyPrintedTokens.push(tok + ' (?)');
                return;
            }
        }
    }
    possibleNextTokens() {
        return [];
    }
    prettyPrint() {
        var wantedString = this.wantedReverse.reverse().map(([a,w,t]) =>
            a.map(x => renderSentence(x)) + '&#8870;' + renderSentence(w)).join('<br>');
        return '<span style="font-family:mono">'+this.prettyPrintedTokens.join(' ')+'<hr>' + 
        wantedString + '</span>' + (this.endedEarly ? 'stopped early' : '');
    }
}
function tokenise(s) {
    // tokens are contiguous chunks of classes of similar characters.
    // similarity classes are:
    // 1. alphanumeric plus #, ', @ is a similarity class
    // 2. brackets ( ) [ ] are each SINGLETON classes
    // 3. other ascii punctuation falls into one class
    // 4. \n is a singleton class
    // Non-newline whitespace is ignored except as a token separator.
    // single line comments start with //
    // multiline comments are /* to */
    // non-ascii characters are invalid outside comments
    var tokens = [];
    for (var i = 0; i < s.length; ++ i) {
        if (s[i] == '/' && i+1 < s.length && s[i+1] == '/') {
            var j = i+2;
            while (j < s.length && s[j] != '\n') ++ j;
            tokens.push(s.slice(i, j));
            i = j-1;
        } else if (s[i] == '/' && i+1 < s.length && s[i+1] == '*') {
            var j = i+2;
            while (j < s.length && !(j+1 < s.length && s[j] == '*' && s[j+1] == '/')) ++ j;
            tokens.push(s.slice(i, j));
            i = j+1;
        } else if (/[_\(\)\[\]!\?\*\|\+&\^%=\>\<\#'@a-zA-Z0-9]/.test(s[i])) {
            var j = i+1;
            while (j < s.length && /[_\|\(\)\[\]!\?\*\+&\^%=\>\<\#'@a-zA-Z0-9]/.test(s[j])) j++;
            tokens.push(s.slice(i,j));
            i=j-1;
        } else if (/\s/.test(s[i])) {
            if (s[i] == '\n') tokens.push('\n');
            continue;
            //} else if (/[\(\)\[\]]/.test(s[i])) {
            //   tokens.push(s[i]);
            //} else if (/[!\?\*&\^%=\>\<]/.test(s[i])) {
            //   var j = i+1;
            //   while (j < s.length && /[!\?\*&\^%=\>\<]/.test(s[j])) j++;
            //   tokens.push(s.slice(i,j));
            //   i=j-1;
        } else tokens.push('<ERROR>');
    }
    return tokens;
}

function updateDisplay() {
    const s = document.getElementById('textInput').value;
    const toks = tokenise(s);
    //console.log(toks);
    //globalProver = new ProverState();
    var helper = new HelperState(globalProver);
    globalProver.importFiles(['leq', 'lt'], () => {
        helper.readTokens(toks);
        document.getElementById('proverOutput').innerHTML = helper.prettyPrint();
    });
    //console.log(prettyPrintHTML(toks));
}
window.userInputUpdated = updateDisplay;
window.documentOnLoad = updateDisplay;
})();
