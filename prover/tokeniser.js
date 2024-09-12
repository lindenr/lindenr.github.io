const TOKEN_PREFIX_OPERATOR = 1, TOKEN_INFIX_OPERATOR = 2, TOKEN_STRICT_VARIABLE = 3, TOKEN_GENERIC = 4, TOKEN_SINGLE_CHAR = 5;

// tokenises, but does no error checking
function tokenizeString(s) {
    var tokens = [];
    const singleCharTokens = new Set(['A', 'E', '(', ')', '[', ']', '@', '#', ',']);
    const operatorChars = new Set(['|', '=', '!', '<', '>', '+', '*', ':', '&', '0', 'S']);
    for (var i = 0; i < s.length;) {
        // start of token is either
        // ' (arity>=3 relation)
        // A forall
        // E exists
        // [a-z] variable
        // @, # start of variable
        // [P-R] generic
        // ()[] brackets
        // otherwise it is an operator
        if (s[i] == "'") {
            const j = i;
            i ++;
            while (i < s.length && s[i] >= 'a' && s[i] <= 'z') ++ i;
            tokens.push([TOKEN_PREFIX_OPERATOR, s.slice(j, i)]);
        } else if (singleCharTokens.has(s[i])) {
            tokens.push([s[i]]);
            i ++;
        } else if (s[i] >= 'a' && s[i] <= 'z') {
            const j = i;
            i ++;
            while (i < s.length && s[i] >= '0' && s[i] <= '9') ++ i;
            tokens.push([TOKEN_STRICT_VARIABLE, s.slice(j, i)]);
        } else if (s[i] >= 'P' && s[i] <= 'Q') {
            const j = i;
            i ++;
            while (i < s.length && s[i] >= '0' && s[i] <= '9') ++ i;
            tokens.push([TOKEN_GENERIC, s.slice(j, i)]);
        } else {
            const j = i;
            i ++;
            while (i < s.length && operatorChars.has(s[i])) ++ i;
            tokens.push([TOKEN_INFIX_OPERATOR, s.slice(j, i)]);
        }
    }
    return tokens;
}

function parseTermTok(toks, from, to, permissive=false) {
    if (from >= to) return undefined;
    var commandFromDepth = [];
    for (var i = from; i < to; ++ i) {
        const tok = toks[i];
        if (tok[0] === TOKEN_PREFIX_OPERATOR) {
            commandFromDepth.push(tok);
        } else if (tok[0] === TOKEN_INFIX_OPERATOR){}
    }
}

