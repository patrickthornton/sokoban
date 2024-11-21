use anyhow::{bail, Context, Result};
use core::time;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::fs::File;
use std::io::{stdin, stdout, BufRead, BufReader, Result as IOResult, Stdout, Write};
use std::path::Path;
use std::thread::sleep;
use termion::cursor::Goto;
use termion::event::Key;
use termion::input::TermRead;
use termion::raw::{IntoRawMode, RawTerminal};

// THINGS TO DO:
// 1. add sleepy behavior; DONE
// 2. add bed behavior; DONE
// 3. add reading level off of file;
//      note that ' ' = grass,
//      # = tree,
//      @ = player,
//      $ = sleepy,
//      and . = bed, with + being player on bed and * being sleepy on bed
//      for you, those will be ' ', T, b, p, _, s, z; DONE
// 4. add all of microban; add level select; DONE
// 5. add undo; DONE
// 6. add color

// turn on/off to enable/disable multiple pushes
// david w. skinner's were designed with this as 'false'
const PUSH_MULTIPLE: bool = false;

// initial size of undo history
const HISTORY_SIZE: usize = 2000;

// convention; first bunny in bunny vector is player
const PLAYER_INDEX: usize = 0;

// constants for the autosolver
const MAX_MOVES: usize = 150;
const MAX_ITERS: usize = 5000000;
const SOLVER_STRUCTURE_SIZE: usize = 1024 * 1024;
const SOLUTION_DISPLAY_SPEED: u64 = 60;

// possible moves
enum Move {
    Up,
    Down,
    Left,
    Right,
}

// possible tile states
#[derive(Debug)]
enum Tile {
    Tree,  // out of bounds
    Grass, // floor; navigable, empty space
    Bed,   // bed; game is won when sleepies -> beds
}

// row then column, down from topleft
type Board = Vec<Vec<Tile>>;

// entity state
type Bunny = (usize, usize);

// previous game state (for history)
struct PreviousState {
    move_no: usize,
    bunnies: Vec<Bunny>,
}

// game state
struct State {
    board: Board,
    bunny_starts: Vec<Bunny>,
    beds: HashSet<Bunny>, // bed positions; ignore that this is Bunny
    bunnies: Vec<Bunny>,  // first bunny in this vector is player
    level_no: usize,
    move_no: usize,
    history: Vec<PreviousState>, // facilitates undo
    won: bool,
}

// autosolver statistics
struct SolveStats {
    iters: usize,
    queue_len: usize,
}

impl State {
    /// create State object from filename and level number
    fn from_file(filename: &str, level_no: usize) -> Result<State> {
        let path = Path::new(filename);
        let f = File::open(path)?;
        let reader = BufReader::new(f);

        let board_rows: Vec<String> = reader.lines().collect::<IOResult<Vec<String>>>()?;
        let mut board_raw: Vec<Vec<u8>> = board_rows
            .iter()
            .map(|row| row.as_bytes().to_vec())
            .collect();

        // first pass to figure out dimensions
        let n_rows = board_raw.len();
        let n_columns = board_raw
            .iter()
            .map(|l| l.len())
            .max()
            .context("should be at least one column")?;
        for row in &mut board_raw {
            row.resize(n_columns, b' ');
        }

        // second pass to grab tiles; iterative, currently
        let mut player: Bunny = (0, 0);
        let mut bunnies: Vec<Bunny> = Vec::with_capacity(20);
        let mut beds: HashSet<Bunny> = HashSet::with_capacity(10);

        let mut board: Vec<Vec<Tile>> = Vec::with_capacity(n_rows);
        for (i, board_row) in board_raw.iter().enumerate() {
            let mut row: Vec<Tile> = Vec::with_capacity(n_columns);
            for (j, board_column) in board_row.iter().enumerate() {
                // read from file; accepts both traditional sokoban
                // notation and this game's letter-based notation
                let tile = match board_column {
                    b'#' | b'T' => Tile::Tree,
                    b' ' => Tile::Grass,
                    b'@' | b'b' => {
                        player = (i, j);
                        Tile::Grass
                    }
                    b'$' | b's' => {
                        bunnies.push((i, j));
                        Tile::Grass
                    }
                    b'.' | b'_' => {
                        beds.insert((i, j));
                        Tile::Bed
                    }
                    b'+' | b'p' => {
                        beds.insert((i, j));
                        player = (i, j);
                        Tile::Bed
                    }
                    b'*' | b'z' => {
                        beds.insert((i, j));
                        bunnies.push((i, j));
                        Tile::Bed
                    }
                    _ => bail!("level file contained unknown character"),
                };
                row.push(tile);
            }
            board.push(row);
        }

        bunnies.push(player);
        bunnies.reverse();

        Ok(State {
            board,
            bunnies: bunnies.clone(),
            bunny_starts: bunnies,
            beds,
            level_no,
            move_no: 0,
            history: Vec::with_capacity(HISTORY_SIZE),
            won: false,
        })
    }

    /// create State object from level number; presumes
    /// file is in levels/{level_no}.txt
    fn from_level_no(level_no: usize) -> Result<State> {
        State::from_file(format!("levels/{}.txt", level_no).as_str(), level_no)
    }

    /// move bunny. returns false if not moved (for instance,
    /// if bunny tried to hop into a tree)
    fn move_bunny(&mut self, bunny_index: usize, m: Move) -> bool {
        let bunny = self
            .bunnies
            .get(bunny_index)
            .expect("bunny oughta be there");
        let dest = match m {
            Move::Up => (bunny.0.saturating_sub(1), bunny.1),
            Move::Down => (bunny.0.saturating_add(1), bunny.1),
            Move::Left => (bunny.0, bunny.1.saturating_sub(1)),
            Move::Right => (bunny.0, bunny.1.saturating_add(1)),
        };

        // out of bounds check
        if self.board.get(dest.0).is_none() || self.board[dest.0].get(dest.1).is_none() {
            return false;
        }

        match self.board[dest.0][dest.1] {
            Tile::Tree => false,
            Tile::Grass | Tile::Bed => {
                let current_state = self.bunnies.clone();

                // push sleepy bunny
                if let Some(bunny_in_the_way_index) =
                    self.bunnies.iter().position(|bunny| dest == *bunny)
                {
                    // in skinner rules, a sleepy bunny can't push another sleepy bunny
                    if !PUSH_MULTIPLE && bunny_index != PLAYER_INDEX {
                        return false;
                    }

                    if !self.move_bunny(bunny_in_the_way_index, m) {
                        return false;
                    }
                }

                // move player bunny
                if bunny_index == PLAYER_INDEX {
                    self.history.push(PreviousState {
                        move_no: self.move_no,
                        bunnies: current_state,
                    });
                    self.move_no += 1;
                }
                self.bunnies[bunny_index] = dest;
                true
            }
        }
    }

    /// set self.won depending on bed conditions.
    /// current win condition is "all sleepy bunnies in bed";
    /// note this is distinct from "all beds have sleepy bunnies in them"
    fn check_win(&mut self) {
        let sleepies_pos = self
            .bunnies
            .get(1..self.bunnies.len())
            .expect("sleepies should be there");
        self.won = sleepies_pos.iter().all(|pos| self.beds.contains(pos));
    }

    /// slimmer, non-mutating version of move_bunny for the solve function;
    /// returns none if no move made
    fn move_bunny_solve(
        &self,
        bunnies: &Vec<Bunny>,
        bunny_index: usize,
        m: Move,
    ) -> Option<Vec<Bunny>> {
        let bunny = bunnies[bunny_index];
        let dest = match m {
            Move::Up => (bunny.0.saturating_sub(1), bunny.1),
            Move::Down => (bunny.0.saturating_add(1), bunny.1),
            Move::Left => (bunny.0, bunny.1.saturating_sub(1)),
            Move::Right => (bunny.0, bunny.1.saturating_add(1)),
        };

        // out of bounds check; skip for perf, assumes board is surrounded with trees
        // if self.board.get(dest.0).is_none() || self.board[dest.0].get(dest.1).is_none() {
        //     return false;
        // }

        match self.board[dest.0][dest.1] {
            Tile::Tree => None,
            Tile::Grass | Tile::Bed => {
                let mut new_bunnies = bunnies.clone();

                // push sleepy bunny
                if let Some(bunny_in_the_way_index) =
                    bunnies.iter().position(|bunny| dest == *bunny)
                {
                    // in skinner rules, a sleepy bunny can't push another sleepy bunny
                    if !PUSH_MULTIPLE && bunny_index != PLAYER_INDEX {
                        return None;
                    }
                    new_bunnies = match self.move_bunny_solve(bunnies, bunny_in_the_way_index, m) {
                        Some(new_bunnies) => new_bunnies,
                        None => return None,
                    }
                }

                // move player bunny
                new_bunnies[bunny_index] = dest;
                Some(new_bunnies)
            }
        }
    }

    /// slimmer, non-mutating version of check_win for solve function
    fn check_win_solve(&self, bunnies: &[Bunny]) -> bool {
        let sleepies_pos = bunnies
            .get(1..bunnies.len())
            .expect("sleepies should be there");
        sleepies_pos.iter().all(|pos| self.beds.contains(pos))
    }

    /// backtracking solver for state; the interesting part of this program,
    /// programming-wise. never uses undo or reset, so starts from current state
    fn solve(
        state: &State,
        max_moves: usize,
        max_iters: usize,
    ) -> Option<(Vec<Vec<Bunny>>, SolveStats)> {
        // storage of previous states
        let mut states: Vec<Vec<Bunny>> = Vec::with_capacity(SOLVER_STRUCTURE_SIZE);
        let mut visited: HashMap<Vec<Bunny>, usize> = HashMap::with_capacity(SOLVER_STRUCTURE_SIZE);

        // all of these use indices for 'states'
        let mut queue: VecDeque<usize> = VecDeque::with_capacity(SOLVER_STRUCTURE_SIZE);
        let mut parents: HashMap<usize, usize> = HashMap::with_capacity(SOLVER_STRUCTURE_SIZE);
        let mut depths: HashMap<usize, usize> = HashMap::with_capacity(SOLVER_STRUCTURE_SIZE);

        let mut iters = 0;

        states.push(state.bunnies.clone());
        visited.insert(state.bunnies.clone(), 0);
        queue.push_back(0);
        depths.insert(0, 1);

        let mut winning_index_opt = None;
        while let Some(new_index) = queue.pop_front() {
            iters += 1;
            let new_state = states[new_index].clone();
            if state.check_win_solve(&new_state) {
                winning_index_opt = Some(new_index);
                break;
            }

            // iters check
            if iters == max_iters {
                break;
            }
            // depth check
            if depths[&new_index] == max_moves {
                continue;
            }

            for bunny_move in [Move::Up, Move::Down, Move::Left, Move::Right] {
                let candidate_state =
                    match state.move_bunny_solve(&new_state, PLAYER_INDEX, bunny_move) {
                        Some(candidate) => candidate,
                        None => continue,
                    };

                if !visited.contains_key(&candidate_state) {
                    states.push(candidate_state.clone());
                    let candidate_index = states.len() - 1;
                    visited.insert(candidate_state, candidate_index);
                    queue.push_back(candidate_index);
                    parents.insert(candidate_index, new_index);
                    depths.insert(candidate_index, depths[&new_index] + 1);
                }
            }
        }

        let mut winning_index = match winning_index_opt {
            Some(winning_index) => winning_index,
            None => return None,
        };
        let mut path: Vec<Vec<Bunny>> = Vec::with_capacity(max_moves);
        path.push(states[winning_index].clone());

        while let Some(path_index) = parents.get(&winning_index) {
            let path_elt = states[*path_index].clone();
            path.push(path_elt);
            winning_index = *path_index;
        }
        path.reverse();

        Some((
            path,
            SolveStats {
                iters,
                queue_len: queue.len(),
            },
        ))
    }
}

// custom print
impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "level {}, move {}.\n\r", self.level_no, self.move_no)?;

        let player_pos = self.bunnies.first().expect("player should be there");
        let sleepies_pos = self
            .bunnies
            .get(1..self.bunnies.len())
            .expect("sleepies should be there");

        for (i, row) in self.board.iter().enumerate() {
            for (j, column) in row.iter().enumerate() {
                // board
                let tile = match column {
                    Tile::Tree => 'T',
                    Tile::Grass => {
                        if (i, j) == *player_pos {
                            'b'
                        } else if sleepies_pos.contains(&(i, j)) {
                            's'
                        } else {
                            ' '
                        }
                    }
                    Tile::Bed => {
                        if (i, j) == *player_pos {
                            'p'
                        } else if sleepies_pos.contains(&(i, j)) {
                            'z'
                        } else {
                            '_'
                        }
                    }
                };

                write!(f, "{}", tile)?;
            }
            writeln!(f, "\r")?;
        }

        writeln!(f)?;
        if self.won {
            writeln!(f, "you got the sleepy bunnies to bed.\r")?;
        } else {
            writeln!(f, "please get the sleepy bunnies to bed.\r")?;
        }
        writeln!(f, "arrow keys to move, z to undo, r to reset.\r")?;
        writeln!(f, "b for last level, n for next level, q to quit.\r")?;
        writeln!(f, "press s if you'd like to see the bunny try it.\n\r")?;

        fmt::Result::Ok(())
    }
}

// update any state metadata and print
fn display(state: &mut State, stdout: &mut RawTerminal<Stdout>) -> Result<()> {
    state.check_win();
    write!(stdout, "{}{}", Goto(1, 1), termion::clear::All)?;
    write!(stdout, "{}", state)?;
    stdout.flush()?;
    Ok(())
}

// main control loop
fn main() -> Result<()> {
    // get stdin and stdout in raw mode;
    // incidentally, raw mode means you need to input carriage returns manually
    let stdin = stdin();
    let mut stdout = stdout().into_raw_mode()?;

    let mut state = State::from_level_no(1)?;
    display(&mut state, &mut stdout)?;

    for keydown in stdin.keys() {
        match keydown? {
            Key::Up => {
                state.move_bunny(PLAYER_INDEX, Move::Up);
            }
            Key::Down => {
                state.move_bunny(PLAYER_INDEX, Move::Down);
            }
            Key::Left => {
                state.move_bunny(PLAYER_INDEX, Move::Left);
            }
            Key::Right => {
                state.move_bunny(PLAYER_INDEX, Move::Right);
            }
            // reset
            Key::Char('r') => {
                state.history.push(PreviousState {
                    move_no: state.move_no,
                    bunnies: state.bunnies.clone(),
                });
                state.bunnies.clone_from(&state.bunny_starts);
                state.move_no = 0;
            }
            // undo
            Key::Char('z') => {
                if let Some(last_state) = state.history.pop() {
                    state.bunnies.clone_from(&last_state.bunnies);
                    state.move_no = last_state.move_no;
                }
            }
            // back one level
            Key::Char('b') => {
                state = State::from_level_no(state.level_no.saturating_sub(1))?;
            }
            // forward one level
            Key::Char('n') => {
                state = State::from_level_no(state.level_no + 1)
                    .context("everyone has gone to bed.")?;
            }
            // solve
            Key::Char('s') => {
                let soln = match State::solve(&state, MAX_MOVES, MAX_ITERS) {
                    Some(soln) => soln,
                    None => {
                        writeln!(stdout, "the bunny couldn't do it from here.\r")?;
                        stdout.flush()?;
                        continue;
                    }
                };

                for elt in soln.0 {
                    state.bunnies = elt;
                    display(&mut state, &mut stdout)?;
                    state.move_no += 1;
                    sleep(time::Duration::from_millis(SOLUTION_DISPLAY_SPEED));
                }
                writeln!(stdout, "iters: {}.\r", soln.1.iters)?;
                writeln!(
                    stdout,
                    "states left in data structure: {}.\r",
                    soln.1.queue_len
                )?;
                stdout.flush()?;
                continue;
            }
            // quit
            Key::Char('q') => break,
            _ => continue,
        };

        display(&mut state, &mut stdout)?;
    }

    write!(stdout, "bye bye !")?;
    stdout.flush()?;
    Ok(())
}
