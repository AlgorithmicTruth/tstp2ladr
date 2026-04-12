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

/* tstp2ladr -- Convert TSTP proofs to LADR format or Prover9 hints.
 *
 * Reads TSTP proofs produced by Vampire, E prover, or Prover9
 * and converts them to:
 *   -ladr  (default) : human-readable Prover9-style proof
 *   -hints           : Prover9 input with proof clauses as hints
 *
 * Links against LADR-2026 libladr.a.
 */

#include "ladr/top_input.h"
#include "ladr/banner.h"
#include "ladr/memory.h"
#include "ladr/clause_misc.h"
#include "ladr/tstp_proof.h"
#include "ladr/tptp_trans.h"
#include "ladr/tptp_parse.h"

#include "fix_positions.h"

#include <string.h>
#include <stdio.h>

#define PROGRAM_NAME "tstp2ladr"
#define VERSION "1.0"

enum { MODE_LADR, MODE_HINTS };

static char Help_string[] =
"\ntstp2ladr -- Convert TSTP proofs to LADR format or Prover9 hints\n"
"\n"
"Usage: tstp2ladr [options] [-f <file>]\n"
"\n"
"Options:\n"
"  -ladr      Output LADR format (default)\n"
"  -hints     Output Prover9 input with proof clauses as hints\n"
"  -p <file>  Use original TPTP problem file for sos/goals (hints mode only)\n"
"  -v         Verbose: print position reconstruction details to stderr\n"
"  -f <file>  Read from file instead of stdin\n"
"  -help      Print this message\n"
"\n"
"Reads TSTP proofs from Vampire, E prover, or Prover9 TSTP output.\n"
"Reconstructs literal and term positions lost in TSTP translation.\n"
"\n"
"Examples:\n"
"  vampire --proof tptp PUZ001-1.p | tstp2ladr\n"
"  eprover --tstp-format -s PUZ001-1.p | tstp2ladr\n"
"\n"
"For Ivy verification:\n"
"  eprover ... | tstp2ladr -hints -p problem.p | prover9 | prooftrans ivy | checker\n"
"\n";

/*************
 *
 *   filter_tstp_input()
 *
 *   Copy TSTP input to a temp file, converting '#' comment lines
 *   to '%' comment lines and stripping SZS delimiter lines.
 *   The LADR parser uses '%' for comments and chokes on '#'.
 *
 *************/

static
FILE *filter_tstp_input(FILE *fin)
{
  FILE *tmp = tmpfile();
  char line[4096];

  if (tmp == NULL) {
    fprintf(stderr, "%s: cannot create temp file\n", PROGRAM_NAME);
    exit(1);
  }

  while (fgets(line, sizeof(line), fin) != NULL) {
    /* Skip SZS delimiter lines */
    if (strstr(line, "SZS output start") != NULL ||
        strstr(line, "SZS output end") != NULL)
      continue;

    /* Convert # comments to % comments */
    if (line[0] == '#') {
      fputc('%', tmp);
      fputs(line + 1, tmp);
    }
    else {
      fputs(line, tmp);
    }
  }

  rewind(tmp);
  return tmp;
}  /* filter_tstp_input */

/*************
 *
 *   main()
 *
 *************/

int main(int argc, char **argv)
{
  int mode = MODE_LADR;
  int verbose = 0;
  FILE *fin = stdin;
  char *filename = NULL;
  char *problem_filename = NULL;
  int n;
  Plist proof;
  int unfixed;
  int answer_attr;

  /* Parse arguments */
  if (string_member("help", argv, argc) ||
      string_member("-help", argv, argc) ||
      string_member("--help", argv, argc)) {
    printf("%s", Help_string);
    exit(0);
  }

  if (string_member("-hints", argv, argc) ||
      string_member("hints", argv, argc))
    mode = MODE_HINTS;

  if (string_member("-ladr", argv, argc) ||
      string_member("ladr", argv, argc))
    mode = MODE_LADR;

  if (string_member("-v", argv, argc) ||
      string_member("-verbose", argv, argc))
    verbose = 1;

  n = which_string_member("-f", argv, argc);
  if (n == -1)
    fin = stdin;
  else if (n + 1 >= argc) {
    fprintf(stderr, "%s: -f requires a filename\n", PROGRAM_NAME);
    exit(1);
  }
  else {
    filename = argv[n + 1];
    fin = fopen(filename, "r");
    if (fin == NULL) {
      fprintf(stderr, "%s: cannot open %s\n", PROGRAM_NAME, filename);
      exit(1);
    }
  }

  n = which_string_member("-p", argv, argc);
  if (n != -1) {
    if (n + 1 >= argc) {
      fprintf(stderr, "%s: -p requires a TPTP problem filename\n",
              PROGRAM_NAME);
      exit(1);
    }
    problem_filename = argv[n + 1];
  }

  /* Initialize LADR subsystems */
  disable_max_megs();
  init_standard_ladr();

  /* Set up TPTP parse types so read_term() can parse TSTP syntax */
  declare_tptp_input_types();
  set_variable_style(PROLOG_STYLE);
  set_quote_char('\'');  /* TSTP uses single-quoted strings */

  /* Register attributes (same set as prooftrans.c) */
  (void) register_attribute("label",        STRING_ATTRIBUTE);
  answer_attr = register_attribute("answer", TERM_ATTRIBUTE);
  (void) register_attribute("props",        TERM_ATTRIBUTE);
  (void) register_attribute("bsub_hint_wt", INT_ATTRIBUTE);
  (void) register_attribute("action",       TERM_ATTRIBUTE);
  (void) register_attribute("action2",      TERM_ATTRIBUTE);
  (void) register_attribute("sine_depth",   INT_ATTRIBUTE);
  declare_term_attribute_inheritable(answer_attr);

  /* Filter input: convert # comments to %, strip SZS delimiters */
  {
    FILE *filtered = filter_tstp_input(fin);
    if (fin != stdin)
      fclose(fin);
    fin = filtered;
  }

  /* Read TSTP proof */
  proof = read_tstp_proof(fin, stderr);
  fclose(fin);

  if (proof == NULL) {
    fprintf(stderr, "%s: no proof steps found\n", PROGRAM_NAME);
    exit(2);
  }

  fprintf(stderr, "%s: read %d proof steps from %s\n",
          PROGRAM_NAME, plist_count(proof),
          filename ? filename : "stdin");

  /* Fix placeholder positions */
  unfixed = fix_proof_positions(proof, verbose);
  if (unfixed > 0)
    fprintf(stderr, "%s: WARNING: %d step(s) have placeholder positions\n",
            PROGRAM_NAME, unfixed);

  /* Output */
  if (mode == MODE_LADR) {
    Plist p;

    print_separator(stdout, "PROOF", TRUE);
    fprintf(stdout, "\n%% Proof converted from TSTP by %s %s\n",
            PROGRAM_NAME, VERSION);
    if (filename)
      fprintf(stdout, "%% Source: %s\n", filename);
    fprintf(stdout, "\n");

    for (p = proof; p; p = p->next)
      fwrite_clause_jmap(stdout, p->v, CL_FORM_STD, NULL);

    print_separator(stdout, "end of proof", TRUE);
  }
  else {
    /* Hints mode: output Prover9 input with proof clauses as hints */
    Plist p;

    /* Prover9 settings */
    fprintf(stdout, "%% Prover9 input with hints from TSTP proof\n");
    fprintf(stdout, "%% Source: %s\n\n", filename ? filename : "stdin");
    fprintf(stdout, "set(prolog_style_variables).\n\n");

    if (problem_filename != NULL) {
      /* Read original TPTP problem file for sos/goals */
      Tptp_input tptp = read_tptp_file(problem_filename);
      if (tptp == NULL) {
        fprintf(stderr, "%s: cannot read TPTP file %s\n",
                PROGRAM_NAME, problem_filename);
        exit(1);
      }
      fprintf(stderr, "%s: read %d assumptions, %d goals from %s\n",
              PROGRAM_NAME,
              plist_count(tptp->assumptions),
              plist_count(tptp->goals),
              problem_filename);

      /* Switch to LADR standard parse types for output
         (FOF formulas need 'all'/'exists' not '!'/'?') */
      clear_parse_type_for_all_symbols();
      declare_standard_parse_types();

      fwrite_formula_list(stdout, tptp->assumptions, "sos");
      if (tptp->goals != NULL)
        fwrite_formula_list(stdout, tptp->goals, "goals");
      fprintf(stdout, "\n");
      zap_tptp_input(tptp);
    }
    else {
      /* sos from proof's INPUT_JUST/DENY_JUST clauses */
      fprintf(stdout, "formulas(sos).\n");
      for (p = proof; p; p = p->next) {
        Topform c = (Topform) p->v;
        Just j = c->justification;
        if (j && (j->type == INPUT_JUST || j->type == DENY_JUST))
          fwrite_clause(stdout, c, CL_FORM_BARE);
      }
      fprintf(stdout, "end_of_list.\n\n");

      /* Goals from proof's GOAL_JUST clauses */
      {
        int has_goals = 0;
        for (p = proof; p; p = p->next) {
          Topform c = (Topform) p->v;
          Just j = c->justification;
          if (j && j->type == GOAL_JUST) {
            if (!has_goals) {
              fprintf(stdout, "formulas(goals).\n");
              has_goals = 1;
            }
            fwrite_clause(stdout, c, CL_FORM_BARE);
          }
        }
        if (has_goals)
          fprintf(stdout, "end_of_list.\n\n");
      }
    }

    /* Hints from proof clauses (same in both cases) */
    fprintf(stdout, "formulas(hints).\n");
    for (p = proof; p; p = p->next) {
      Topform c = (Topform) p->v;
      if (!c->is_formula && c->literals != NULL)
        fwrite_clause(stdout, c, CL_FORM_BARE);
    }
    fprintf(stdout, "end_of_list.\n\n");
  }

  exit(0);
}  /* main */
