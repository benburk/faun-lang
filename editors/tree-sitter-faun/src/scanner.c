// What `crates/faun/src/lex.rs` reads by looking past a token: where a line
// ends, and whether a name's `!` is its own.
//
// The grammar allows a line end only after what a line can end with, and
// never inside a bracket but a method block's `.( )` and a block's `( )`.
// What is left is the next line's first token: a line break ends the line
// unless that token carries it on, as `.`, an infix operator, `where`, `if`
// or a closing bracket does. A `-` carries it on only where space follows
// it; held to what follows, it negates.
//
// A name's trailing `!` makes it an effect's, unless it begins `!=`.
//
// The scanner keeps no state: the brackets are the parser's.

#include "tree_sitter/parser.h"

enum TokenType { NEWLINE, EFFECT_IDENTIFIER };

void *tree_sitter_faun_external_scanner_create(void) { return NULL; }

void tree_sitter_faun_external_scanner_destroy(void *payload) { (void)payload; }

unsigned tree_sitter_faun_external_scanner_serialize(void *payload, char *buffer) {
  (void)payload;
  (void)buffer;
  return 0;
}

void tree_sitter_faun_external_scanner_deserialize(void *payload, const char *buffer,
                                                   unsigned length) {
  (void)payload;
  (void)buffer;
  (void)length;
}

static bool is_space(int32_t c) { return c == ' ' || c == '\t' || c == '\r' || c == '\n'; }

static bool is_word_char(int32_t c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
         c == '_';
}

// Whether `word` is next, whole.
static bool next_is_word(TSLexer *lexer, const char *word) {
  for (const char *c = word; *c; c++) {
    if (lexer->lookahead != *c) {
      return false;
    }
    lexer->advance(lexer, false);
  }
  return !is_word_char(lexer->lookahead);
}

// Whether a line beginning here goes on with the line before.
static bool continues_line(TSLexer *lexer) {
  switch (lexer->lookahead) {
    case ')':
    case ']':
    case '}':
    case '.':
    case '?':
    case ':':
    case '=':
    case '<':
    case '>':
    case '+':
    case '*':
    case '/':
    case '%':
    case '&':
    case '|':
    case '^':
      return true;
    case '!':
      lexer->advance(lexer, false);
      return lexer->lookahead == '=';
    case '-':
      lexer->advance(lexer, false);
      return lexer->lookahead == '>' || lexer->lookahead == '#' || is_space(lexer->lookahead) ||
             lexer->eof(lexer);
    case 'w':
      return next_is_word(lexer, "where");
    case 'i':
      return next_is_word(lexer, "if");
    default:
      return false;
  }
}

// From a line break: the break and the space after it, if the line ends. A
// comment after that is left to be read as one, but looked past for the next
// line's first token.
static bool scan_newline(TSLexer *lexer) {
  while (is_space(lexer->lookahead)) {
    lexer->advance(lexer, false);
  }
  lexer->mark_end(lexer);
  for (;;) {
    if (lexer->lookahead == '#') {
      while (!lexer->eof(lexer) && lexer->lookahead != '\n') {
        lexer->advance(lexer, false);
      }
    } else if (is_space(lexer->lookahead)) {
      lexer->advance(lexer, false);
    } else {
      break;
    }
  }
  if (lexer->eof(lexer) || continues_line(lexer)) {
    return false;
  }
  lexer->result_symbol = NEWLINE;
  return true;
}

static bool scan_effect_identifier(TSLexer *lexer) {
  if (!(lexer->lookahead >= 'a' && lexer->lookahead <= 'z') && lexer->lookahead != '_') {
    return false;
  }
  while (is_word_char(lexer->lookahead)) {
    lexer->advance(lexer, false);
  }
  if (lexer->lookahead != '!') {
    return false;
  }
  lexer->advance(lexer, false);
  if (lexer->lookahead == '=') {
    return false;
  }
  lexer->result_symbol = EFFECT_IDENTIFIER;
  return true;
}

bool tree_sitter_faun_external_scanner_scan(void *payload, TSLexer *lexer,
                                            const bool *valid_symbols) {
  (void)payload;
  while (lexer->lookahead == ' ' || lexer->lookahead == '\t' || lexer->lookahead == '\r') {
    lexer->advance(lexer, true);
  }
  if (lexer->lookahead == '\n') {
    if (valid_symbols[NEWLINE]) {
      return scan_newline(lexer);
    }
    while (is_space(lexer->lookahead)) {
      lexer->advance(lexer, true);
    }
  }
  if (valid_symbols[EFFECT_IDENTIFIER]) {
    return scan_effect_identifier(lexer);
  }
  return false;
}
