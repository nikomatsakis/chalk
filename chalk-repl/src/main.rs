#![cfg(not(test))]

#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate failure;

use std::fs::File;
use std::io::Read;
use std::process::exit;

use chalk_solve::ext::*;
use chalk_solve::SolverChoice;
use chalk_integration::db::ChalkDatabase;
use chalk_integration::lowering::*;
use chalk_integration::query::LoweringDatabase;
use docopt::Docopt;
use failure::Fallible;

use rustyline::error::ReadlineError;

const USAGE: &'static str = "
chalk repl

Usage:
  chalki [options]
  chalki (-h | --help)

Options:
  --help              Show this screen.
  --program=PATH      Specifies the path to the `.chalk` file containing traits/impls.
  --goal=GOAL         Specifies a goal to evaluate (may be given more than once).
  --overflow-depth=N  Specifies the overflow depth [default: 10].
  --no-cache          Disable caching.
";

/// This struct represents the various command line options available.
#[derive(Debug, Deserialize)]
struct Args {
    flag_program: Option<String>,
    flag_goal: Vec<String>,
    flag_overflow_depth: usize,
    flag_no_cache: bool,
}

/// A loaded and parsed program.
struct LoadedProgram {
    text: String,
    db: ChalkDatabase,
}

impl LoadedProgram {
    /// Creates a new Program struct, given a `.chalk` file as a String and
    /// a [`SolverChoice`].
    ///
    /// [`SolverChoice`]: struct.solve.SolverChoice.html
    fn new(text: String, solver_choice: SolverChoice) -> Fallible<LoadedProgram> {
        let db = ChalkDatabase::with(&text, solver_choice);
        Ok(LoadedProgram { text, db })
    }

    /// Parse a goal and attempt to solve it, using the specified solver.
    fn goal(&self, text: &str) -> Fallible<()> {
        let program = self.db.checked_program()?;
        let goal = chalk_parse::parse_goal(text)?.lower(&*program)?;
        let peeled_goal = goal.into_peeled_goal();
        match self.db.solve(&peeled_goal) {
            Some(v) => println!("{}\n", v),
            None => println!("No possible solution.\n"),
        }
        Ok(())
    }
}

fn run() -> Fallible<()> {
    // Parse the command line arguments.
    let args: &Args = &Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());

    // Validate arguments.
    if args.flag_overflow_depth == 0 {
        eprintln!("error: overflow depth must be at least 1");
        exit(1);
    }

    // Load the .chalk file, if given.
    let mut prog = None;
    if let Some(program) = &args.flag_program {
        match load_program(args, program) {
            Ok(p) => prog = Some(p),
            Err(err) => {
                eprintln!("error loading program: {}", err);
                exit(1);
            }
        }
    }

    if args.flag_goal.is_empty() {
        // The user specified no goal. Enter interactive mode.
        readline_loop(&mut rustyline::Editor::new(), "?- ", |rl, line| {
            if let Err(e) = process(args, line, rl, &mut prog) {
                eprintln!("error: {}", e);
            }
        })
    } else {
        // Check that a program was provided.
        // TODO: It's customary to print Usage info when an error like this
        // happens.
        let prog = prog.ok_or(format_err!(
            "error: cannot eval without a program; use `--program` to specify one."
        ))?;

        // Evaluate the goal(s). If any goal returns an error, print the error
        // and exit.
        prog.db.with_program(|_| -> Fallible<()> {
            for g in &args.flag_goal {
                if let Err(e) = prog.goal(g) {
                    eprintln!("error: {}", e);
                    exit(1);
                }
            }
            Ok(())
        })?;

        Ok(())
    }
}

/// Reads input lines from the user. Lines start with the string given by `prompt`.
/// Each line the user enters is passed to the function `f` for processing.
///
/// The loop terminates (and the program ends) when EOF is reached or if an error
/// occurs while reading the next line.
fn readline_loop<F>(rl: &mut rustyline::Editor<()>, prompt: &str, mut f: F) -> Fallible<()>
where
    F: FnMut(&mut rustyline::Editor<()>, &str),
{
    loop {
        match rl.readline(prompt) {
            Ok(line) => {
                // Save the line to the history list.
                rl.add_history_entry(&line);

                // Process the line.
                f(rl, &line);
            }

            // EOF: We're done.
            Err(ReadlineError::Eof) => break,

            // Some other error occured.
            Err(e) => Err(e)?,
        }
    }

    Ok(())
}

/// Process a single command. `args` is a struct containing the command-line
/// arguments, and `prog` is a parsed `.chalk` file.
// TODO: Could we pass in an Options struct or something? The Args struct
// still has Strings where it should have Enums... (e.g. solver_choice)
fn process(
    args: &Args,
    command: &str,
    rl: &mut rustyline::Editor<()>,
    prog: &mut Option<LoadedProgram>,
) -> Fallible<()> {
    if command == "help" || command == "h" {
        // Print out interpreter commands.
        // TODO: Implement "help <command>" for more specific help.
        help()
    } else if command == "program" {
        // Load a .chalk file via stdin, until EOF is found.
        *prog = Some(LoadedProgram::new(read_program(rl)?, args.solver_choice())?);
    } else if command.starts_with("load ") {
        // Load a .chalk file.
        let filename = &command["load ".len()..];
        *prog = Some(load_program(args, filename)?);
    } else if command.starts_with("debug ") {
        match command.split_whitespace().nth(1) {
            Some(level) => std::env::set_var("CHALK_DEBUG", level),
            None => println!("debug <level> set debug level to <level>"),
        }
    } else {
        // The command is either "print", "lowered", or a goal.

        // Check that a program has been loaded.
        let prog = prog.as_ref().ok_or(format_err!(
            "no program currently loaded; type 'help' to see available commands"
        ))?;

        // Attempt to parse the program.
        prog.db.with_program(|_| -> Fallible<()> {
            match command {
                // Print out the loaded program.
                "print" => println!("{}", prog.text),

                // TODO: Write a line of documentation here.
                "lowered" => println!("{:#?}", prog.db.environment()),

                // Assume this is a goal.
                // TODO: Print out "type 'help' to see available commands" if it
                // fails to parse?
                _ => prog.goal(command)?,
            }
            Ok(())
        })?
    }

    Ok(())
}

/// Load the file into a string, and parse it.
// TODO: Could we pass in an Options struct or something? The Args struct
// still has Strings where it should have Enums... (e.g. solver_choice)
fn load_program(args: &Args, filename: &str) -> Fallible<LoadedProgram> {
    let mut text = String::new();
    File::open(filename)?.read_to_string(&mut text)?;
    Ok(LoadedProgram::new(text, args.solver_choice())?)
}

/// Print out help for commands in interpreter mode.
// TODO: Implement "help <command>" for more info.
fn help() {
    println!("Commands:");
    println!("  help          print this output");
    println!("  program       provide a program via stdin");
    println!("  load <file>   load program from <file>");
    println!("  print         print the current program");
    println!("  lowered       print the lowered program");
    println!("  <goal>        attempt to solve <goal>");
    println!("  debug <level> set debug level to <level>");
}

/// Read a program from the command-line. Stop reading when EOF is read. If
/// an error occurs while reading, a `Err` is returned.
fn read_program(rl: &mut rustyline::Editor<()>) -> Fallible<String> {
    println!("Enter a program; press Ctrl-D when finished");
    let mut text = String::new();
    readline_loop(rl, "| ", |_, line| {
        text += line;
        text += "\n";
    })?;
    Ok(text)
}

impl Args {
    fn solver_choice(&self) -> SolverChoice {
        SolverChoice::SLG {
            max_size: self.flag_overflow_depth,
        }
    }
}

fn main() {
    use std::io::Write;

    ::std::process::exit(match run() {
        Ok(_) => 0,
        Err(ref e) => {
            write!(&mut ::std::io::stderr(), "{}", e).expect("Error writing to stderr");
            1
        }
    });
}
