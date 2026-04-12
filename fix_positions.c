/*  Copyright (C) 2026 Jeffrey Machado

    This file is part of tstp2ladr.

    tstp2ladr is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License, version 2.

    tstp2ladr is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with tstp2ladr; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
*/

#include "fix_positions.h"
#include "ladr/unify.h"
#include "ladr/subsume.h"
#include "ladr/literals.h"
#include "ladr/term.h"
#include "ladr/ioutil.h"
#include "ladr/clauses.h"
#include "ladr/memory.h"

#include <string.h>
#include <stdlib.h>

/* ================================================================
 * Helper: renumber variables in a term to use consecutive
 * numbers starting from 0.  apply() creates variables with
 * numbers like multiplier*MAX_VARS + varnum, which can exceed
 * MAX_VARS and corrupt context arrays.  This function walks
 * the term tree and renumbers in-place.
 *
 * vmap[i] maps old variable number to new.  -1 means unmapped.
 * *next_var is the next available new variable number.
 * ================================================================ */

static
void renumber_vars_term(Term t, int *vmap, int vmap_size, int *next_var)
{
  if (VARIABLE(t)) {
    int vn = VARNUM(t);
    if (vn >= 0 && vn < vmap_size) {
      if (vmap[vn] < 0)
        vmap[vn] = (*next_var)++;
      /* Modify variable number in place.
         VARNUM(t) = t->private_symbol for variables (>= 0). */
      t->private_symbol = vmap[vn];
    }
    return;
  }
  else {
    int i;
    for (i = 0; i < ARITY(t); i++)
      renumber_vars_term(ARG(t, i), vmap, vmap_size, next_var);
  }
}  /* renumber_vars_term */

/* Renumber all variables in a clause to use 0, 1, 2, ... */
static
void renumber_clause_vars(Topform c)
{
  /* Enough for 2 contexts worth of vars */
  int vmap_size = MAX_VARS * 3;
  int *vmap;
  int next_var = 0;
  Literals lit;
  int i;

  vmap = (int *) malloc(vmap_size * sizeof(int));
  for (i = 0; i < vmap_size; i++)
    vmap[i] = -1;

  for (lit = c->literals; lit; lit = lit->next)
    renumber_vars_term(lit->atom, vmap, vmap_size, &next_var);

  free(vmap);
  c->normal_vars = TRUE;
}  /* renumber_clause_vars */

/* ================================================================
 * Helper: build the resolvent of c1 (removing lit n1) and c2
 * (removing lit n2), applying substitution from contexts, and
 * check if it matches the actual result r.
 *
 * Literal positions are 1-based.
 * ================================================================ */

static
BOOL verify_resolvent(Topform c1, int n1, Topform c2, int n2,
                      Topform r, Context ctx1, Context ctx2)
{
  /* Build a temporary clause with the remaining literals. */
  Topform expected = get_topform();
  Literals prev = NULL;
  Literals lits;
  int i;
  BOOL ok;

  /* Copy literals from c1, skipping literal n1 */
  i = 1;
  for (lits = c1->literals; lits; lits = lits->next, i++) {
    if (i != n1) {
      Term a = apply(lits->atom, ctx1);
      Literals new_lit = get_literals();
      new_lit->sign = lits->sign;
      new_lit->atom = a;
      new_lit->next = NULL;
      if (prev)
        prev->next = new_lit;
      else
        expected->literals = new_lit;
      prev = new_lit;
    }
  }

  /* Copy literals from c2, skipping literal n2 */
  i = 1;
  for (lits = c2->literals; lits; lits = lits->next, i++) {
    if (i != n2) {
      Term a = apply(lits->atom, ctx2);
      Literals new_lit = get_literals();
      new_lit->sign = lits->sign;
      new_lit->atom = a;
      new_lit->next = NULL;
      if (prev)
        prev->next = new_lit;
      else
        expected->literals = new_lit;
      prev = new_lit;
    }
  }

  renumber_clause_vars(expected);

  /* Check mutual subsumption (equivalent up to variable renaming) */
  ok = subsumes(expected, r) && subsumes(r, expected);

  zap_topform(expected);
  return ok;
}  /* verify_resolvent */

/* ================================================================
 * Fix binary resolution positions.
 *
 * BINARY_RES_JUST stores u.lst = [c1_id, n1, c2_id, n2]
 * where n1 and n2 are literal positions (1-based).
 *
 * We try all pairs of opposite-sign literals, unify, and
 * verify the resolvent matches.
 * ================================================================ */

static
BOOL fix_binary_res(Topform step, Plist proof, int verbose)
{
  Just j = step->justification;
  Ilist lst = j->u.lst;
  int c1_id, c2_id;
  Topform c1, c2;
  int i, k;
  Literals li, lk;

  if (lst == NULL || lst->next == NULL ||
      lst->next->next == NULL || lst->next->next->next == NULL)
    return FALSE;

  c1_id = lst->i;
  c2_id = lst->next->next->i;

  c1 = proof_id_to_clause(proof, c1_id);
  c2 = proof_id_to_clause(proof, c2_id);
  if (c1 == NULL || c2 == NULL)
    return FALSE;

  /* Skip formula (non-clausal) parents */
  if (c1->is_formula || c2->is_formula)
    return FALSE;

  for (i = 1, li = c1->literals; li; i++, li = li->next) {
    for (k = 1, lk = c2->literals; lk; k++, lk = lk->next) {
      if (li->sign != lk->sign) {
        Context ctx1 = get_context();
        Context ctx2 = get_context();
        Trail trail = NULL;

        if (unify(li->atom, ctx1, lk->atom, ctx2, &trail)) {
          if (verify_resolvent(c1, i, c2, k, step, ctx1, ctx2)) {
            /* Found the right pair -- update positions */
            lst->next->i = i;
            lst->next->next->next->i = k;
            undo_subst(trail);
            free_context(ctx1);
            free_context(ctx2);
            if (verbose)
              fprintf(stderr, "%% Fixed resolution step %llu: "
                      "lits %d,%d\n", step->id, i, k);
            return TRUE;
          }
          undo_subst(trail);
        }
        free_context(ctx1);
        free_context(ctx2);
      }
    }
  }

  /* Special case: equality resolution (same clause, x != x resolved) */
  if (c1_id == c2_id) {
    for (i = 1, li = c1->literals; li; i++, li = li->next) {
      if (!li->sign && eq_term(li->atom)) {
        Context ctx = get_context();
        Trail trail = NULL;
        if (unify(ARG(li->atom, 0), ctx, ARG(li->atom, 1), ctx, &trail)) {
          /* This could be an xxres that was mapped as binary_res */
          undo_subst(trail);
          free_context(ctx);
          /* Just set the literal position */
          lst->next->i = i;
          lst->next->next->next->i = i;
          if (verbose)
            fprintf(stderr, "%% Fixed eq-resolution step %llu: "
                    "lit %d\n", step->id, i);
          return TRUE;
        }
        free_context(ctx);
      }
    }
  }

  return FALSE;
}  /* fix_binary_res */

/* ================================================================
 * Fix paramodulation positions.
 *
 * PARA_JUST stores u.para with from_id, into_id, from_pos, into_pos.
 * from_pos = [literal, side, ...] where side is 1 (left) or 2 (right).
 * into_pos = [literal, subterm_path...]
 *
 * We try all equality literals in from_clause, both sides,
 * and all subterm positions in into_clause, looking for a
 * unifiable pair whose result matches the step.
 * ================================================================ */

/* Helper: enumerate all subterm positions in a term as
   Plist of Ilist position vectors. Position vectors are
   1-based arg indices. Empty list = the term itself. */

static
void enumerate_positions_rec(Term t, Ilist prefix, Plist *result)
{
  int i;
  /* Add current position */
  *result = plist_append(*result, copy_ilist(prefix));

  for (i = 0; i < ARITY(t); i++) {
    Ilist ext = ilist_append(copy_ilist(prefix), i + 1);
    enumerate_positions_rec(ARG(t, i), ext, result);
    zap_ilist(ext);
  }
}  /* enumerate_positions_rec */

static
Plist enumerate_positions(Term t)
{
  Plist result = NULL;
  enumerate_positions_rec(t, NULL, &result);
  return result;
}  /* enumerate_positions */

/* Helper: build expected paramodulant and verify against result.
   from_clause has equality literal eq_lit_num, with matched side
   alpha at from_side (0=left, 1=right) and replacement beta.
   into_clause has literal into_lit_num, and the target subterm
   is at into_pos within that literal's atom. */

static
BOOL verify_paramod(Topform from_cl, int eq_lit_num, int from_side,
                    Topform into_cl, int into_lit_num, Ilist into_pos,
                    Topform result, Context ctx1, Context ctx2)
{
  /* Build expected result by copying into_clause with the
     target subterm replaced by apply(beta, ctx1). */
  Topform expected = get_topform();
  Literals prev = NULL;
  Literals lits;
  Literals eq_lit;
  Term beta;
  int i;
  BOOL ok;

  eq_lit = ith_literal(from_cl->literals, eq_lit_num);
  if (eq_lit == NULL)
    return FALSE;

  /* beta is the non-matched side */
  beta = ARG(eq_lit->atom, 1 - from_side);

  i = 1;
  for (lits = into_cl->literals; lits; lits = lits->next, i++) {
    Term a;
    Literals new_lit;

    if (i == into_lit_num) {
      /* This literal contains the target -- apply substitution
         with replacement */
      a = apply_substitute2(lits->atom, beta, ctx1, into_pos, ctx2);
    }
    else {
      a = apply(lits->atom, ctx2);
    }

    new_lit = get_literals();
    new_lit->sign = lits->sign;
    new_lit->atom = a;
    new_lit->next = NULL;
    if (prev)
      prev->next = new_lit;
    else
      expected->literals = new_lit;
    prev = new_lit;
  }

  renumber_clause_vars(expected);

  ok = subsumes(expected, result) && subsumes(result, expected);

  zap_topform(expected);
  return ok;
}  /* verify_paramod */

static
BOOL fix_paramod(Topform step, Plist proof, int verbose)
{
  Just j = step->justification;
  Parajust pj = j->u.para;
  int from_id, into_id;
  Topform from_cl, into_cl;
  int eq_lit_num;
  Literals eq_lit;

  if (pj == NULL)
    return FALSE;

  from_id = (int) pj->from_id;
  into_id = (int) pj->into_id;

  from_cl = proof_id_to_clause(proof, from_id);
  into_cl = proof_id_to_clause(proof, into_id);
  if (from_cl == NULL || into_cl == NULL)
    return FALSE;
  if (from_cl->is_formula || into_cl->is_formula)
    return FALSE;

  /* Try each positive equality literal in from_clause */
  eq_lit_num = 1;
  for (eq_lit = from_cl->literals; eq_lit; eq_lit = eq_lit->next, eq_lit_num++) {
    int side;
    if (!eq_lit->sign || !eq_term(eq_lit->atom))
      continue;

    for (side = 0; side <= 1; side++) {
      Term alpha = ARG(eq_lit->atom, side);      /* matched side */
      int into_lit_num;
      Literals into_lit;

      into_lit_num = 1;
      for (into_lit = into_cl->literals; into_lit;
           into_lit = into_lit->next, into_lit_num++) {
        /* Enumerate subterm positions in this literal's atom */
        Plist positions = enumerate_positions(into_lit->atom);
        Plist pp;

        for (pp = positions; pp; pp = pp->next) {
          Ilist pos = (Ilist) pp->v;
          Term target = term_at_pos(into_lit->atom, pos);

          if (target != NULL && !VARIABLE(target)) {
            Context ctx1 = get_context();
            Context ctx2 = get_context();
            Trail trail = NULL;

            if (unify(alpha, ctx1, target, ctx2, &trail)) {
              if (verify_paramod(from_cl, eq_lit_num, side,
                                 into_cl, into_lit_num, pos,
                                 step, ctx1, ctx2)) {
                /* Success -- update positions */
                Ilist new_from_pos;
                Ilist new_into_pos;

                new_from_pos = ilist_append(NULL, eq_lit_num);
                new_from_pos = ilist_append(new_from_pos, side + 1);

                new_into_pos = ilist_prepend(copy_ilist(pos), into_lit_num);

                zap_ilist(pj->from_pos);
                zap_ilist(pj->into_pos);
                pj->from_pos = new_from_pos;
                pj->into_pos = new_into_pos;

                undo_subst(trail);
                free_context(ctx1);
                free_context(ctx2);

                /* Clean up remaining positions */
                {
                  Plist q;
                  for (q = positions; q; q = q->next)
                    zap_ilist((Ilist) q->v);
                  zap_plist(positions);
                }

                if (verbose)
                  fprintf(stderr, "%% Fixed paramod step %llu: "
                          "from lit %d side %d, into lit %d\n",
                          step->id, eq_lit_num, side + 1, into_lit_num);
                return TRUE;
              }
              undo_subst(trail);
            }
            free_context(ctx1);
            free_context(ctx2);
          }
        }

        /* Clean up positions for this literal */
        {
          Plist q;
          for (q = positions; q; q = q->next)
            zap_ilist((Ilist) q->v);
          zap_plist(positions);
        }
      }
    }
  }

  return FALSE;
}  /* fix_paramod */

/* ================================================================
 * Fallback: try to re-interpret a PARA_JUST as BINARY_RES_JUST.
 *
 * External provers (especially E) sometimes label resolution steps
 * as "pm" (paramodulation).  If paramod position reconstruction
 * fails, try to treat the step as binary resolution.  If that
 * succeeds, convert the justification type.
 * ================================================================ */

static
BOOL try_para_as_resolution(Topform step, Plist proof, int verbose)
{
  Just j = step->justification;
  Parajust pj = j->u.para;
  int c1_id, c2_id;
  Topform c1, c2;
  int i, k;
  Literals li, lk;

  if (pj == NULL)
    return FALSE;

  c1_id = (int) pj->from_id;
  c2_id = (int) pj->into_id;

  c1 = proof_id_to_clause(proof, c1_id);
  c2 = proof_id_to_clause(proof, c2_id);
  if (c1 == NULL || c2 == NULL)
    return FALSE;
  if (c1->is_formula || c2->is_formula)
    return FALSE;

  for (i = 1, li = c1->literals; li; i++, li = li->next) {
    for (k = 1, lk = c2->literals; lk; k++, lk = lk->next) {
      if (li->sign != lk->sign) {
        Context ctx1 = get_context();
        Context ctx2 = get_context();
        Trail trail = NULL;

        if (unify(li->atom, ctx1, lk->atom, ctx2, &trail)) {
          if (verify_resolvent(c1, i, c2, k, step, ctx1, ctx2)) {
            /* Convert from PARA_JUST to BINARY_RES_JUST */
            zap_ilist(pj->from_pos);
            zap_ilist(pj->into_pos);
            free_mem(pj, PTRS(sizeof(struct parajust)));

            j->type = BINARY_RES_JUST;
            j->u.lst = ilist_append(
                         ilist_append(
                           ilist_append(
                             ilist_append(NULL, c1_id), i),
                           c2_id), k);

            undo_subst(trail);
            if (verbose)
              fprintf(stderr, "%% Re-interpreted paramod step %llu as "
                      "resolution: lits %d,%d\n", step->id, i, k);
            free_context(ctx1);
            free_context(ctx2);
            return TRUE;
          }
          undo_subst(trail);
        }
        free_context(ctx1);
        free_context(ctx2);
      }
    }
  }

  return FALSE;
}  /* try_para_as_resolution */

/* ================================================================
 * Fix factoring positions.
 *
 * FACTOR_JUST stores u.lst = [parent_id, lit1, lit2]
 * where lit1 and lit2 are the two unified literals (1-based).
 * The result is the parent with lit2 removed.
 * ================================================================ */

static
BOOL fix_factor(Topform step, Plist proof, int verbose)
{
  Just j = step->justification;
  Ilist lst = j->u.lst;
  int parent_id;
  Topform parent;
  int i, k;
  Literals li, lk;

  if (lst == NULL || lst->next == NULL || lst->next->next == NULL)
    return FALSE;

  parent_id = lst->i;
  parent = proof_id_to_clause(proof, parent_id);
  if (parent == NULL || parent->is_formula)
    return FALSE;

  for (i = 1, li = parent->literals; li; i++, li = li->next) {
    for (k = i + 1, lk = ith_literal(parent->literals, i + 1); lk;
         k++, lk = lk->next) {
      if (li->sign == lk->sign) {
        Context ctx = get_context();
        Trail trail = NULL;

        if (unify(li->atom, ctx, lk->atom, ctx, &trail)) {
          /* Build expected result: parent with lit k removed, subst applied */
          Topform expected = get_topform();
          Literals prev = NULL;
          Literals scan;
          int idx;
          BOOL ok;

          idx = 1;
          for (scan = parent->literals; scan; scan = scan->next, idx++) {
            if (idx != k) {
              Term a = apply(scan->atom, ctx);
              Literals new_lit = get_literals();
              new_lit->sign = scan->sign;
              new_lit->atom = a;
              new_lit->next = NULL;
              if (prev)
                prev->next = new_lit;
              else
                expected->literals = new_lit;
              prev = new_lit;
            }
          }

          renumber_clause_vars(expected);
          ok = subsumes(expected, step) && subsumes(step, expected);
          zap_topform(expected);

          if (ok) {
            lst->next->i = i;
            lst->next->next->i = k;
            undo_subst(trail);
            free_context(ctx);
            if (verbose)
              fprintf(stderr, "%% Fixed factor step %llu: "
                      "lits %d,%d\n", step->id, i, k);
            return TRUE;
          }
          undo_subst(trail);
        }
        free_context(ctx);
      }
    }
  }

  return FALSE;
}  /* fix_factor */

/* ================================================================
 * Fix XXRES positions.
 *
 * XXRES_JUST stores u.lst = [parent_id, lit_num]
 * where lit_num is the negative equality literal (x != x) resolved.
 * ================================================================ */

static
BOOL fix_xxres(Topform step, Plist proof, int verbose)
{
  Just j = step->justification;
  Ilist lst = j->u.lst;
  int parent_id;
  Topform parent;
  int i;
  Literals lit;

  if (lst == NULL || lst->next == NULL)
    return FALSE;

  parent_id = lst->i;
  parent = proof_id_to_clause(proof, parent_id);
  if (parent == NULL || parent->is_formula)
    return FALSE;

  for (i = 1, lit = parent->literals; lit; i++, lit = lit->next) {
    if (!lit->sign && eq_term(lit->atom)) {
      Context ctx = get_context();
      Trail trail = NULL;

      if (unify(ARG(lit->atom, 0), ctx, ARG(lit->atom, 1), ctx, &trail)) {
        /* Build expected: parent with lit i removed, subst applied */
        Topform expected = get_topform();
        Literals prev = NULL;
        Literals scan;
        int idx;
        BOOL ok;

        idx = 1;
        for (scan = parent->literals; scan; scan = scan->next, idx++) {
          if (idx != i) {
            Term a = apply(scan->atom, ctx);
            Literals new_lit = get_literals();
            new_lit->sign = scan->sign;
            new_lit->atom = a;
            new_lit->next = NULL;
            if (prev)
              prev->next = new_lit;
            else
              expected->literals = new_lit;
            prev = new_lit;
          }
        }

        renumber_clause_vars(expected);
        ok = subsumes(expected, step) && subsumes(step, expected);
        zap_topform(expected);

        if (ok) {
          lst->next->i = i;
          undo_subst(trail);
          free_context(ctx);
          if (verbose)
            fprintf(stderr, "%% Fixed xxres step %llu: lit %d\n",
                    step->id, i);
          return TRUE;
        }
        undo_subst(trail);
      }
      free_context(ctx);
    }
  }

  return FALSE;
}  /* fix_xxres */

/* ================================================================
 * Fix hyper/UR resolution positions.
 *
 * HYPER_RES_JUST / UR_RES_JUST store u.lst as:
 *   [nuc_id, nuc_lit1, sat1_id, sat1_lit, nuc_lit2, sat2_id, sat2_lit, ...]
 *
 * Each triplet after the nucleus ID represents one satellite:
 *   nuc_lit = position of resolved literal in nucleus
 *   sat_id  = satellite clause ID
 *   sat_lit = position of resolved literal in satellite
 *
 * We fix each satellite's literal positions similarly to binary
 * resolution, but incrementally against the nucleus.
 * ================================================================ */

static
BOOL fix_hyper_ur(Topform step, Plist proof, int verbose)
{
  Just j = step->justification;
  Ilist lst = j->u.lst;
  int nuc_id;
  Topform nuc;
  Ilist p;
  BOOL all_ok = TRUE;

  if (lst == NULL)
    return FALSE;

  nuc_id = lst->i;
  nuc = proof_id_to_clause(proof, nuc_id);
  if (nuc == NULL || nuc->is_formula)
    return FALSE;

  /* Process each satellite triplet */
  p = lst->next;
  while (p && p->next && p->next->next) {
    int sat_id = p->next->i;
    Topform sat = proof_id_to_clause(proof, sat_id);

    if (sat != NULL && !sat->is_formula) {
      /* Try all pairs of opposite-sign literals */
      int ni, si;
      Literals nlit, slit;
      BOOL found = FALSE;

      for (ni = 1, nlit = nuc->literals; nlit && !found;
           ni++, nlit = nlit->next) {
        for (si = 1, slit = sat->literals; slit && !found;
             si++, slit = slit->next) {
          if (nlit->sign != slit->sign) {
            Context ctx1 = get_context();
            Context ctx2 = get_context();
            Trail trail = NULL;

            if (unify(nlit->atom, ctx1, slit->atom, ctx2, &trail)) {
              /* Accept first unifiable pair for this satellite */
              p->i = ni;             /* nuc_lit position */
              p->next->next->i = si; /* sat_lit position */
              found = TRUE;
              if (verbose)
                fprintf(stderr, "%% Fixed hyper/ur step %llu: "
                        "nuc_lit %d, sat %d lit %d\n",
                        step->id, ni, sat_id, si);
            }
            undo_subst(trail);
            free_context(ctx1);
            free_context(ctx2);
          }
        }
      }
      if (!found)
        all_ok = FALSE;
    }
    else {
      all_ok = FALSE;
    }

    p = p->next->next->next;  /* advance to next triplet */
  }

  return all_ok;
}  /* fix_hyper_ur */

/* ================================================================
 * Fix flip positions (secondary justification).
 *
 * FLIP_JUST stores u.id = literal_num (1-based).
 * The result has one equality literal flipped compared to
 * the primary parent.
 * ================================================================ */

static
BOOL fix_flip(Topform step, Just flip_just, Plist proof, int verbose)
{
  /* Find the primary parent from the chain */
  Just primary = step->justification;
  int parent_id;
  Topform parent;
  int i;
  Literals plit, slit;

  if (primary == NULL)
    return FALSE;

  /* Get parent ID from primary justification */
  switch (primary->type) {
  case COPY_JUST:
  case BACK_DEMOD_JUST:
  case BACK_UNIT_DEL_JUST:
    parent_id = (int) primary->u.id;
    break;
  default:
    return FALSE;  /* can't determine parent for flip */
  }

  parent = proof_id_to_clause(proof, parent_id);
  if (parent == NULL || parent->is_formula)
    return FALSE;

  /* Find which literal was flipped by comparing */
  i = 1;
  plit = parent->literals;
  slit = step->literals;
  while (plit && slit) {
    if (plit->sign == slit->sign && eq_term(plit->atom) && eq_term(slit->atom)) {
      /* Check if this literal is flipped (args swapped) */
      if (term_ident(ARG(plit->atom, 0), ARG(slit->atom, 1)) &&
          term_ident(ARG(plit->atom, 1), ARG(slit->atom, 0))) {
        flip_just->u.id = i;
        if (verbose)
          fprintf(stderr, "%% Fixed flip in step %llu: lit %d\n",
                  step->id, i);
        return TRUE;
      }
    }
    i++;
    plit = plit->next;
    slit = slit->next;
  }

  return FALSE;
}  /* fix_flip */

/* ================================================================
 * Fix merge positions (secondary justification).
 *
 * MERGE_JUST stores u.id = literal_num (1-based) of the
 * duplicate literal that was removed.
 * ================================================================ */

static
BOOL fix_merge(Topform step, Just merge_just, Plist proof, int verbose)
{
  /* For merge, the removed literal is a duplicate.
     We can't easily determine which one without the parent,
     so leave it as-is for now. */
  (void) step; (void) merge_just; (void) proof; (void) verbose;
  return FALSE;
}  /* fix_merge */

/* ================================================================
 * Public: fix_proof_positions()
 *
 * Iterate over all proof steps and fix placeholder positions
 * in their justifications.  Returns number of unfixed steps.
 * ================================================================ */

/* ================================================================
 * Expand non-propositional COPY_JUST steps.
 *
 * E prover produces nested inferences like:
 *   inference(cn,[],[inference(rw,[],[inference(pm,[],[A,B]), C])])
 * The parser extracts all parent IDs [A,B,C] but the outermost
 * rule "cn" maps to COPY_JUST which stores only the first parent A.
 * The inner inference rules and parents B,C are lost.
 *
 * This results in COPY_JUST steps where the child is NOT a
 * propositional consequence of the (single) parent.  expand_proof_ivy()
 * converts these to PROPOSITIONAL_JUST which the Ivy checker rejects.
 *
 * Fix: for each such step, find unit clauses in the proof that can
 * resolve away the "extra" literals in the parent to produce the
 * child.  Create intermediate BINARY_RES_JUST steps.
 * ================================================================ */

/* Helper: build a resolvent of c1 (removing literal at position n1)
   with c2 (removing literal at position n2), applying the unifying
   substitution.  Returns a new Topform with the resolvent clause
   and a BINARY_RES_JUST justification.  Assigns the given ID. */

static
Topform build_resolvent(Topform c1, int n1, Topform c2, int n2, int id)
{
  Context ctx1 = get_context();
  Context ctx2 = get_context();
  Trail trail = NULL;
  Literals l1 = ith_literal(c1->literals, n1);
  Literals l2 = ith_literal(c2->literals, n2);
  Topform resolvent;
  Literals prev;
  Literals scan;
  int idx;

  if (l1 == NULL || l2 == NULL)
    return NULL;

  if (!unify(l1->atom, ctx1, l2->atom, ctx2, &trail)) {
    free_context(ctx1);
    free_context(ctx2);
    return NULL;
  }

  resolvent = get_topform();
  prev = NULL;

  /* Copy literals from c1, skipping n1 */
  idx = 1;
  for (scan = c1->literals; scan; scan = scan->next, idx++) {
    if (idx != n1) {
      Term a = apply(scan->atom, ctx1);
      Literals new_lit = get_literals();
      new_lit->sign = scan->sign;
      new_lit->atom = a;
      new_lit->next = NULL;
      if (prev) prev->next = new_lit;
      else resolvent->literals = new_lit;
      prev = new_lit;
    }
  }

  /* Copy literals from c2, skipping n2 */
  idx = 1;
  for (scan = c2->literals; scan; scan = scan->next, idx++) {
    if (idx != n2) {
      Term a = apply(scan->atom, ctx2);
      Literals new_lit = get_literals();
      new_lit->sign = scan->sign;
      new_lit->atom = a;
      new_lit->next = NULL;
      if (prev) prev->next = new_lit;
      else resolvent->literals = new_lit;
      prev = new_lit;
    }
  }

  undo_subst(trail);
  free_context(ctx1);
  free_context(ctx2);

  renumber_clause_vars(resolvent);

  resolvent->id = id;
  resolvent->justification = binary_res_just_by_id(c1->id, n1, c2->id, n2);
  upward_clause_links(resolvent);

  return resolvent;
}  /* build_resolvent */

/* Recursive backtracking search to find a chain of unit resolutions
   that transforms 'current' into 'target'.
   On success, the intermediate steps are in *chain (prepended, reversed).
   Returns TRUE if a chain was found. */

static
BOOL find_resolution_chain(Topform current, Topform target,
                           Plist proof, Plist before,
                           Plist extra_units,
                           int *next_id, int depth,
                           Plist *chain, int verbose)
{
  int li;
  Literals lit;
  Topform cpy;

  /* Base case: check if current matches target */
  cpy = copy_clause(current);
  renumber_clause_vars(cpy);

  if ((target->literals == NULL && cpy->literals == NULL) ||
      (target->literals != NULL && cpy->literals != NULL &&
       subsumes(cpy, target) && subsumes(target, cpy))) {
    zap_topform(cpy);
    return TRUE;
  }
  zap_topform(cpy);

  /* Depth limit */
  if (depth > 20 || current->literals == NULL)
    return FALSE;

  /* Try each literal in current */
  for (li = 1, lit = current->literals; lit; li++, lit = lit->next) {
    /* Try each unit clause in proof */
    Plist q;
    for (q = proof; q != before; q = q->next) {
      Topform u = (Topform) q->v;
      if (u->is_formula) continue;
      if (number_of_literals(u->literals) != 1) continue;
      if (u->literals->sign == lit->sign) continue;

      {
        Topform resolvent = build_resolvent(current, li, u, 1, *next_id);
        if (resolvent != NULL) {
          /* Recursively try to complete the chain */
          (*next_id)++;
          if (find_resolution_chain(resolvent, target, proof, before,
                                    extra_units, next_id, depth + 1,
                                    chain, verbose)) {
            *chain = plist_prepend(*chain, resolvent);
            return TRUE;
          }
          /* Backtrack: undo this resolution */
          (*next_id)--;
          zap_topform(resolvent);
        }
      }
    }

    /* Also try extra_units (intermediate steps from earlier expansions) */
    for (q = extra_units; q; q = q->next) {
      Topform u = (Topform) q->v;
      if (u->is_formula) continue;
      if (number_of_literals(u->literals) != 1) continue;
      if (u->literals->sign == lit->sign) continue;

      {
        Topform resolvent = build_resolvent(current, li, u, 1, *next_id);
        if (resolvent != NULL) {
          (*next_id)++;
          if (find_resolution_chain(resolvent, target, proof, before,
                                    extra_units, next_id, depth + 1,
                                    chain, verbose)) {
            *chain = plist_prepend(*chain, resolvent);
            return TRUE;
          }
          (*next_id)--;
          zap_topform(resolvent);
        }
      }
    }
  }

  return FALSE;
}  /* find_resolution_chain */

/* PUBLIC */
int expand_nonprop_copies(Plist *proof_ptr, int verbose)
{
  Plist proof = *proof_ptr;
  Plist new_proof = NULL;  /* build backward, reverse at end */
  int next_id;
  int expanded = 0;
  Plist p;

  next_id = greatest_id_in_proof(proof) + 1;

  for (p = proof; p; p = p->next) {
    Topform step = (Topform) p->v;
    Just j = step->justification;
    Topform parent;

    if (j == NULL || j->type != COPY_JUST || step->is_formula) {
      new_proof = plist_prepend(new_proof, step);
      continue;
    }

    parent = proof_id_to_clause(proof, j->u.id);
    if (parent == NULL || parent->is_formula) {
      new_proof = plist_prepend(new_proof, step);
      continue;
    }

    /* Check if child is propositional consequence of parent.
       subsumes(parent, step) means parent's literals are a subset
       of step's (under some substitution). */
    if (subsumes(parent, step)) {
      new_proof = plist_prepend(new_proof, step);
      continue;
    }

    if (verbose) {
      fprintf(stderr, "%% Step %llu: COPY from %llu, parent has %d lits, "
              "child has %d lits\n",
              (unsigned long long) step->id,
              (unsigned long long) j->u.id,
              number_of_literals(parent->literals),
              number_of_literals(step->literals));
    }

    /* Non-propositional: try to find resolution chain with backtracking */
    {
      Plist chain = NULL;
      int saved_next_id = next_id;

      if (find_resolution_chain(parent, step, proof, p,
                                new_proof, &next_id, 0,
                                &chain, verbose)) {
        Plist q;
        int last_id;

        /* Insert intermediate steps into new_proof */
        last_id = parent->id;
        for (q = chain; q; q = q->next) {
          Topform intermediate = (Topform) q->v;
          new_proof = plist_prepend(new_proof, intermediate);
          last_id = intermediate->id;
        }
        zap_plist(chain);  /* free list nodes, not the Topforms */

        /* Replace step's COPY_JUST to reference the last intermediate */
        j->u.id = last_id;
        new_proof = plist_prepend(new_proof, step);
        expanded++;

        if (verbose)
          fprintf(stderr, "%% Expanded COPY step %llu: %d resolution(s)\n",
                  (unsigned long long) step->id,
                  next_id - saved_next_id);
      }
      else {
        /* Failed to find chain -- restore next_id and keep as is */
        next_id = saved_next_id;
        new_proof = plist_prepend(new_proof, step);
        if (verbose)
          fprintf(stderr, "%% WARNING: could not expand non-propositional "
                  "COPY step %llu\n", (unsigned long long) step->id);
      }
    }
  }

  new_proof = reverse_plist(new_proof);
  zap_plist(proof);  /* free old Plist nodes (shallow) */
  *proof_ptr = new_proof;
  return expanded;
}  /* expand_nonprop_copies */

/* ================================================================
 * Public: fix_proof_positions()
 *
 * Iterate over all proof steps and fix placeholder positions
 * in their justifications.  Returns number of unfixed steps.
 * ================================================================ */

/* PUBLIC */
int fix_proof_positions(Plist proof, int verbose)
{
  Plist p;
  int failures = 0;
  int fixed = 0;
  int skipped = 0;

  for (p = proof; p; p = p->next) {
    Topform step = (Topform) p->v;
    Just j = step->justification;
    BOOL ok;

    if (j == NULL)
      continue;

    /* Skip formula (non-clausal) steps entirely */
    if (step->is_formula) {
      skipped++;
      continue;
    }

    switch (j->type) {
    case BINARY_RES_JUST:
      ok = fix_binary_res(step, proof, verbose);
      if (ok) fixed++;
      else {
        failures++;
        if (verbose)
          fprintf(stderr, "%% WARNING: could not fix positions for "
                  "step %llu (binary_res), using placeholders\n",
                  step->id);
      }
      break;

    case PARA_JUST:
    case PARA_FX_JUST:
    case PARA_IX_JUST:
    case PARA_FX_IX_JUST:
      ok = fix_paramod(step, proof, verbose);
      if (!ok)
        ok = try_para_as_resolution(step, proof, verbose);
      if (ok) fixed++;
      else {
        failures++;
        if (verbose)
          fprintf(stderr, "%% WARNING: could not fix positions for "
                  "step %llu (paramod), using placeholders\n",
                  step->id);
      }
      break;

    case FACTOR_JUST:
      ok = fix_factor(step, proof, verbose);
      if (ok) fixed++;
      else {
        failures++;
        if (verbose)
          fprintf(stderr, "%% WARNING: could not fix positions for "
                  "step %llu (factor), using placeholders\n",
                  step->id);
      }
      break;

    case XXRES_JUST:
      ok = fix_xxres(step, proof, verbose);
      if (ok) fixed++;
      else {
        failures++;
        if (verbose)
          fprintf(stderr, "%% WARNING: could not fix positions for "
                  "step %llu (xxres), using placeholders\n",
                  step->id);
      }
      break;

    case HYPER_RES_JUST:
    case UR_RES_JUST:
      ok = fix_hyper_ur(step, proof, verbose);
      if (ok) fixed++;
      else {
        failures++;
        if (verbose)
          fprintf(stderr, "%% WARNING: could not fix positions for "
                  "step %llu (hyper/ur), using placeholders\n",
                  step->id);
      }
      break;

    default:
      /* INPUT_JUST, GOAL_JUST, DENY_JUST, CLAUSIFY_JUST, COPY_JUST,
         DEMOD_JUST, etc.: no positions to fix */
      skipped++;
      break;
    }

    /* Also check secondary justifications (flip, merge, etc.) */
    {
      Just sec;
      for (sec = j->next; sec; sec = sec->next) {
        switch (sec->type) {
        case FLIP_JUST:
          fix_flip(step, sec, proof, verbose);
          break;
        case MERGE_JUST:
          fix_merge(step, sec, proof, verbose);
          break;
        default:
          break;
        }
      }
    }
  }

  if (verbose)
    fprintf(stderr, "%% Position fixing: %d fixed, %d failed, %d skipped\n",
            fixed, failures, skipped);

  return failures;
}  /* fix_proof_positions */
