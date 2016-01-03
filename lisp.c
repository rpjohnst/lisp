#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stddef.h>

/* values */

enum type {
	t_atom, t_cons, t_number
};

typedef uintptr_t value;

struct atom {
	size_t length;
	char name[];
};

struct cons {
	value a;
	value d;
};

enum type tag(value x) {
	return x & 0x3;
}

void *ptr(value x) {
	return (void*)(x & ~0x3);
}

const value nil = 0 | t_atom;

/* symbols */

int atom_cmp(const struct atom *a, const struct atom *b) {
	if (a->length != b->length)
		return (int)a->length - (int)b->length;
	return memcmp(a->name, b->name, a->length);
}

struct tree {
	struct tree *left;
	struct tree *right;
	struct atom atom;
};

struct tree *insert(struct tree **root, struct tree *node) {
	if (*root == NULL) {
		*root = node;
		return node;
	}

	int cmp = atom_cmp(&node->atom, &(*root)->atom);
	if (cmp < 0)
		return insert(&(*root)->left, node);
	else if (cmp > 0)
		return insert(&(*root)->right, node);
	else
		return *root;
}

value mk_atom(struct tree **symbols, size_t length, const char *name) {
	struct tree *node = malloc(sizeof(*node) + length);
	node->left = node->right = NULL;
	node->atom.length = length;
	memcpy(node->atom.name, name, length);

	struct tree *inserted = insert(symbols, node);
	if (inserted != node)
		free(node);

	return (uintptr_t)&inserted->atom | t_atom;
}

/* interpreter state */

struct interpreter {
	struct tree *symbols;

	struct cons *heap;
	size_t capacity;
	size_t size;

	double *num_heap;
	size_t num_capacity;
	size_t num_size;

	// internals
	value prim;
	value proc;

	// builtins
	value quote;
	value cond;
	value lambda;

	value t;

	// primitives
	value atom;
	value number;
	value eq;
	value car;
	value cdr;
	value cons;
};

void interpreter_init(struct interpreter *i) {
	i->symbols = NULL;

	i->heap = malloc(512 * sizeof(*i->heap));
	i->capacity = 512;
	i->size = 0;

	i->num_heap = malloc(512 * sizeof(*i->num_heap));
	i->num_capacity = 512;
	i->num_size = 0;

#define insert(a) i->a = mk_atom(&i->symbols, strlen(#a), #a)
#define insert_sym(a, b) i->a = mk_atom(&i->symbols, strlen(b), b)
	insert_sym(prim, "&prim");
	insert_sym(proc, "&proc");
	insert(quote);
	insert(cond);
	insert(lambda);

	insert(t);

	insert_sym(atom, "atom?");
	insert_sym(number, "number?");
	insert_sym(eq, "eq?");
	insert(car);
	insert(cdr);
	insert(cons);
#undef insert
#undef insert_sym
}

/* built-ins */

value atom(const struct interpreter *i, value x) {
	return tag(x) == t_atom || tag(x) == t_number ? i->t : nil;
}

value number(const struct interpreter *i, value x) {
	return tag(x) == t_number ? i->t : nil;
}

value eq(const struct interpreter *i, value x, value y) {
	return x == y ? i->t : nil;
}

value car(value x) {
	assert(tag(x) == t_cons);
	const struct cons *c = ptr(x);
	return c->a;
}

value cdr(value x) {
	assert(tag(x) == t_cons);
	const struct cons *c = ptr(x);
	return c->d;
}

value caar(value x) { return car(car(x)); }
value cadr(value x) { return car(cdr(x)); }
value cadar(value x) { return car(cdr(car(x))); }
value caddr(value x) { return car(cdr(cdr(x))); }
value caddar(value x) { return car(cdr(cdr(car(x)))); }
value cadddr(value x) { return car(cdr(cdr(cdr(x)))); }

value cons(struct interpreter *i, value a, value d) {
	assert(i->size < i->capacity);

	struct cons *cell = &i->heap[i->size];
	i->size++;

	cell->a = a;
	cell->d = d;

	return (uintptr_t)cell | t_cons;
}

value mk_number(struct interpreter *i, double n) {
	assert(i->num_size < i->num_capacity);

	double *c = &i->num_heap[i->num_size];
	i->num_size++;

	*c = n;

	return (uintptr_t)c | t_number;
}

/* interpreter */

value append(struct interpreter *i, value x, value y) {
	if (x == nil)
		return y;

	return cons(i, car(x), append(i, cdr(x), y));
}

value list(struct interpreter *i, value x, value y) {
	return cons(i, x, cons(i, y, nil));
}

value pair(struct interpreter *i, value x, value y) {
	if (x == nil && y == nil) return nil;
	if (atom(i, x) != i->t && atom(i, y) != i->t)
		return cons(i, list(i, car(x), car(y)), pair(i, cdr(x), cdr(y)));
	assert(0);
}

value assoc(const struct interpreter *i, value x, value env) {
	assert(env != nil);

	if (eq(i, caar(env), x) == i->t)
		return cadar(env);
	else
		return assoc(i, x, cdr(env));
}

value eval(struct interpreter *i, value exp, value env);

value apply(struct interpreter *i, value fun, value args, value env) {
	if (eq(i, car(fun), i->prim) == i->t) {
		if (eq(i, cadr(fun), i->atom) == i->t) return atom(i, car(args));
		if (eq(i, cadr(fun), i->eq) == i->t) return eq(i, car(args), cadr(args));
		if (eq(i, cadr(fun), i->car) == i->t) return car(car(args));
		if (eq(i, cadr(fun), i->cdr) == i->t) return cdr(car(args));
		if (eq(i, cadr(fun), i->cons) == i->t) return cons(i, car(args), cadr(args));
	}

	if (eq(i, car(fun), i->proc) == i->t)
		return eval(i, cadddr(fun), append(i, pair(i, caddr(fun), args), cadr(fun)));

	assert(0);
}

value evcond(struct interpreter *i, value c, value env) {
	if (eval(i, caar(c), env) == i->t) return eval(i, cadar(c), env);
	return evcond(i, cdr(c), env);
}

value evlist(struct interpreter *i, value m, value env) {
	if (m == nil) return nil;
	return cons(i, eval(i, car(m), env), evlist(i, cdr(m), env));
}

value eval(struct interpreter *i, value exp, value env) {
	if (atom(i, exp) == i->t) {
		if (number(i, exp)) return exp;
		return assoc(i, exp, env);
	}

	if (eq(i, car(exp), i->quote) == i->t) return cadr(exp);
	if (eq(i, car(exp), i->cond) == i->t) return evcond(i, cdr(exp), env);
	if (eq(i, car(exp), i->lambda) == i->t) return cons(i, i->proc, cons(i, env, cdr(exp)));

	return apply(i, eval(i, car(exp), env), evlist(i, cdr(exp), env), env);
}

/* repl */

struct token {
	enum { tok_eof, tok_lparen, tok_rparen, tok_quote, tok_dot, tok_number, tok_symbol } kind;
	value atom;
};

struct parser {
	FILE *file;
};

void parser_init(struct parser *p, struct interpreter *i, FILE *file) {
	p->file = file;
}

struct token token(struct parser *p, struct interpreter *i) {
	int c;
	do {
		c = fgetc(p->file);
	} while (isspace(c));

	switch (c) {
	case EOF: return (struct token){ tok_eof, nil };
	case '(': return (struct token){ tok_lparen, nil };
	case ')': return (struct token){ tok_rparen, nil };
	case '\'': return (struct token){ tok_quote, nil };
	case '.': return (struct token){ tok_dot, nil };
	}

	char atom[80], *a = atom;
	do {
		*a++ = c;
		c = fgetc(p->file);
	} while (c != EOF && !isspace(c) && c != '(' && c != ')');

	ungetc(c, p->file);
	*a = '\0';

	char *end;
	double num = strtod(atom, &end);
	if (end == a)
		return (struct token){ tok_number, mk_number(i, num) };
	else
		return (struct token){ tok_symbol, mk_atom(&i->symbols, a - atom, atom) };
}

value read(struct parser *p, struct interpreter *i, struct token current);

value read_list(struct parser *p, struct interpreter *i) {
	struct token current = token(p, i);

	if (current.kind == tok_rparen)
		return nil;
	else if (current.kind == tok_dot) {
		value t = read(p, i, token(p, i));
		assert(token(p, i).kind == tok_rparen);
		return t;
	} else {
		value head = read(p, i, current);
		value tail = read_list(p, i);
		return cons(i, head, tail);
	}
}

value read(struct parser *p, struct interpreter *i, struct token current) {
	if (current.kind == tok_lparen)
		return read_list(p, i);
	if (current.kind == tok_quote)
		return list(i, i->quote, read(p, i, token(p, i)));

	return current.atom;
}

void print(const struct interpreter *i, value exp) {
	if (atom(i, exp) == i->t) {
		if (eq(i, exp, nil))
			printf("()");
		else if (number(i, exp)) {
			const double *n = ptr(exp);
			printf("%f", *n);
		} else {
			const struct atom *a = ptr(exp);
			printf("%.*s", (int)a->length, a->name);
		}
	} else if (eq(i, car(exp), i->prim) == i->t || eq(i, car(exp), i->proc) == i->t) {
		printf("<proc:%zx>", (uintptr_t)ptr(exp));
	} else {
		printf("(");
		for (value v = exp; v != nil; v = cdr(v)) {
			print(i, car(v));
			if (cdr(v) != nil)
				printf(" ");
		}
		printf(")");
	}
}

int main(void) {
	struct interpreter interp, *i = &interp;
	interpreter_init(i);

	struct parser parser, *p = &parser;
	parser_init(p, i, stdin);

	value env = cons(i,
		list(i, i->atom, list(i, i->prim, i->atom)), cons(i,
		list(i, i->eq, list(i, i->prim, i->eq)), cons(i,
		list(i, i->car, list(i, i->prim, i->car)), cons(i,
		list(i, i->cdr, list(i, i->prim, i->cdr)), cons(i,
		list(i, i->cons, list(i, i->prim, i->cons)), nil)))));

	for (;;) {
		printf("> ");
		fflush(stdout);

		struct token current = token(p, i);
		if (current.kind == tok_eof) {
			printf("\n");
			break;
		}

		value exp = read(p, i, current);
		print(i, eval(i, exp, env));
		printf("\n");
	}
}
