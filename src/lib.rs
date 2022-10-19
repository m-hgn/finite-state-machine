//! # finite_state_machine
//! Model deterministic finite automata and run them!

use std::result::Result;

use fnv::FnvHashMap;
use fnv::FnvHashSet;
use std::collections::hash_map::Entry::Vacant;
use std::hash::Hash;

/// State machine encapsulating the Tuple (Q, q0, Sigma, F, Delta)
/// - The finite set of states (Q) `states`,
/// - The initial state (q0) `initial_state`,
/// - The finite set of input symbols (Sigma) `symbols`,
/// - The set of accept states (F) `accept_states`,
/// - The transition functions (Delta) `transitions`,
///   defined in terms of a state and an input symbol.
#[derive(Debug)]
pub struct DFA<StateIdT, SymbolT> {
    pub states: FnvHashSet<StateIdT>,
    pub initial_state: Option<StateIdT>,
    pub symbols: FnvHashSet<SymbolT>,
    pub accept_states: FnvHashSet<StateIdT>,
    pub transitions: FnvHashMap<(StateIdT, SymbolT), StateIdT>,
}

/// Enum representing the Accepted, Denied and Unfinished \
/// states of running input through a DFA
#[derive(Debug, PartialEq, Eq)]
pub enum RunResult {
    Accept,
    Deny,
    Unfinished,
}

impl<StateIdT, SymbolT> Default for DFA<StateIdT, SymbolT>
where
    StateIdT: Hash + Eq + Copy,
    SymbolT: Hash + Eq + Copy,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<StateIdT, SymbolT> DFA<StateIdT, SymbolT>
where
    StateIdT: Hash + Eq + Copy,
    SymbolT: Hash + Eq + Copy,
{
    /// Create a new DFA with no states or transitions.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// ```
    pub fn new() -> DFA<StateIdT, SymbolT> {
        DFA {
            states: fnv::FnvHashSet::default(),
            initial_state: None,
            symbols: fnv::FnvHashSet::default(),
            accept_states: fnv::FnvHashSet::default(),
            transitions: fnv::FnvHashMap::default(),
        }
    }

    /// Remove a state from a DFAs set of states.
    ///
    /// - Note that transitions are user managed,
    ///   transitions containing a removed state
    ///   will not automatically be removed
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // Add a new state with ID 0
    /// dfa.add_state(0).unwrap();
    ///
    /// // Remove state 0
    /// assert!(dfa.remove_state(0).is_ok());
    ///
    /// // Removing non-existent state fails
    /// assert!(dfa.remove_state(100).is_err());
    /// ```
    pub fn remove_state(&mut self, state: StateIdT) -> Result<(), &str> {
        if self.states.contains(&state) {
            self.states.remove(&state);
            if self.accept_states.contains(&state) {
                self.accept_states.remove(&state);
            }
            if let Some(initial_state) = self.initial_state {
                if initial_state == state {
                    self.initial_state = None;
                }
            }
            Ok(())
        } else {
            Err("State with given ID is not present in set of states.")
        }
    }

    /// Add a state to a DFAs set of states.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // Add a new state with ID 0:
    /// assert!(dfa.add_state(0).is_ok());
    ///
    /// // Try to add state that already exists:
    /// assert!(dfa.add_state(0).is_err());
    /// ```
    pub fn add_state(&mut self, state: StateIdT) -> Result<(), &str> {
        if !self.states.contains(&state) {
            self.states.insert(state);
            Ok(())
        } else {
            Err("State with given ID is already present in set of states.")
        }
    }

    /// Add a vector of values to the symbols of the DFA
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // DFAs input alphabet should be {a, b, c}
    /// let symbols = vec!['a', 'b', 'c'];
    ///
    /// // Add symbols
    /// assert!(dfa.add_symbols(symbols).is_ok());
    ///
    /// // Includes already existing symbol 'a'
    /// let symbols = vec!['a', 'd', 'e'];
    ///
    /// // Adding symbols fails, 'a' is already a symbol
    /// assert!(dfa.add_symbols(symbols).is_err());
    /// ```
    pub fn add_symbols(&mut self, symbols: Vec<SymbolT>) -> Result<(), &str> {
        for &symbol in &symbols {
            if !self.symbols.contains(&symbol) {
                self.symbols.insert(symbol);
            } else {
                return Err("Symbol is already present in set of symbols.");
            }
        }
        Ok(())
    }

    /// Set transition from state with valid input symbol to other state.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // DFAs input alphabet should be {a, b, c}
    /// let symbols = vec!['a', 'b', 'c'];
    /// dfa.add_symbols(symbols).unwrap();
    ///
    /// // DFA has states 0, 1 and 2
    /// for i in 0..3 {
    ///     dfa.add_state(i).unwrap();
    /// }
    ///
    /// // From state 0 with input 'a', go to state 2
    /// let status = dfa.set_transition((0, 'a'), 2);
    /// assert!(status.is_ok());
    ///
    /// // Redefine transition from state 0 with input 'a'
    /// let status = dfa.set_transition((0, 'a'), 1);
    /// assert!(status.is_ok());
    ///
    /// // Defining transition for non-existent states fails
    /// let status = dfa.set_transition((100, 'a'), 101);
    /// assert!(status.is_err());
    ///
    /// // Defining transition for invalid input symbol fails
    /// let status = dfa.set_transition((0, 'G'), 1);
    /// assert!(status.is_err());
    /// ```
    pub fn set_transition(
        &mut self,
        input: (StateIdT, SymbolT),
        result_state: StateIdT,
    ) -> Result<(), &str> {
        let (start_state, symbol) = input;
        if !self.symbols.contains(&symbol) {
            return Err("Provided symbol not in DFAs set of symbols.");
        } else if !self.states.contains(&start_state) || !self.states.contains(&result_state) {
            return Err("Provided state(s) not in DFAs set of states.");
        }

        if let Vacant(e) = self.transitions.entry(input) {
            e.insert(result_state);
        } else if self.transitions.get(&input) == Some(&result_state) {
            return Ok(());
        } else {
            self.transitions.remove(&input);
            self.transitions.insert(input, result_state);
        }
        Ok(())
    }

    /// Declare an existing state as accepting.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // Add state 0
    /// dfa.add_state(0).unwrap();
    ///
    /// // Declare state 0 as accepting
    /// assert!(dfa.set_accept_state(0).is_ok());
    ///
    /// // Declaring non-existent state as accepting fails
    /// assert!(dfa.set_accept_state(100).is_err());
    /// ```
    pub fn set_accept_state(&mut self, state: StateIdT) -> Result<(), &str> {
        if self.states.contains(&state) {
            if !self.accept_states.contains(&state) {
                self.accept_states.insert(state);
            }
            Ok(())
        } else {
            Err("Given state is not in DFAs set of states.")
        }
    }

    /// Declare an existing state as not accepting.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // Add states 0 and 1
    /// dfa.add_state(0).unwrap();
    /// dfa.add_state(1).unwrap();
    ///
    /// // Declare state 0 as accepting
    /// dfa.set_accept_state(0).unwrap();
    ///
    /// // Declare accepting state 0 as non accepting
    /// assert!(dfa.set_non_accept_state(0).is_ok());
    ///
    /// // Declare already non accepting state 1 as non-
    /// // accepting. This succeeds but doesn't do anything
    /// assert!(dfa.set_non_accept_state(1).is_ok());
    ///
    /// // Declaring non-existent state as non accepting fails
    /// assert!(dfa.set_non_accept_state(100).is_err());
    /// ```
    pub fn set_non_accept_state(&mut self, state: StateIdT) -> Result<(), &str> {
        if self.states.contains(&state) {
            if self.accept_states.contains(&state) {
                self.accept_states.remove(&state);
                Ok(())
            } else {
                Ok(())
            }
        } else {
            Err("Given state is not in DFAs set of states.")
        }
    }

    /// Set the initial state of the DFA.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // Add state 0
    /// dfa.add_state(0).unwrap();
    ///
    /// // Set state 0 as initial state
    /// assert!(dfa.set_initial_state(0).is_ok());
    ///
    /// // Setting non-existent state as initial state fails
    /// assert!(dfa.set_initial_state(100).is_err());
    /// ```
    pub fn set_initial_state(&mut self, state: StateIdT) -> Result<(), &str> {
        if self.states.contains(&state) {
            self.initial_state = Some(state);
            Ok(())
        } else {
            Err("Given state is not in DFAs set of states.")
        }
    }

    /// Simulate a single step using one input symbol and
    /// the current state to recieve the resulting state.
    /// If there is a valid resulting state, returns
    /// Ok(Some), if the symbol does not correspond to a
    /// valid transition, returns Ok(None).
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // DFAs input alphabet should be {a, b, c}
    /// let symbols = vec!['a', 'b', 'c'];
    /// dfa.add_symbols(symbols).unwrap();
    ///
    /// // DFA has states 0, 1 and 2
    /// for i in 0..3 {
    ///     dfa.add_state(i).unwrap();
    /// }
    ///
    /// // From state 0 with input 'a', go to state 1
    /// dfa.set_transition((0, 'a'), 1).unwrap();
    ///
    /// // From state 1 with input 'b', go to state 2
    /// dfa.set_transition((1, 'b'), 2).unwrap();
    ///
    /// // Simulate step from state 0 with symbol 'a'
    /// // to state 1.
    /// let result_state = dfa.step(0, 'a');
    /// assert!(result_state.is_ok());
    ///
    /// // Get resulting StateID,
    /// // 1 is expected in this case
    /// assert_eq!(result_state.unwrap().unwrap(), 1 as u16);
    ///
    /// // Stepping from a valid state using an
    /// // undefined transition doesn't fail but
    /// // returns None as result state
    /// let result_state = dfa.step(0, 'c');
    /// assert_eq!(result_state, Ok(None));
    ///
    /// // Stepping with invalid symbol fails.
    /// let result_state = dfa.step(0, 'Z');
    /// assert!(result_state.is_err());
    ///
    /// // Stepping from a non-existent state fails.
    /// let result_state = dfa.step(100, 'a');
    /// assert!(result_state.is_err());
    /// ```
    pub fn step(&mut self, state: StateIdT, symbol: SymbolT) -> Result<Option<StateIdT>, &str> {
        if self.states.contains(&state) {
            if self.symbols.contains(&symbol) {
                let result_state = self.transitions.get(&(state, symbol));
                match result_state {
                    Some(result_state) => Ok(Some(*result_state)),
                    None => Ok(None),
                }
            } else {
                Err("Input not in DFAs set of symbols.")
            }
        } else {
            Err("Given state is not in DFAs set of states.")
        }
    }

    /// Run the DFA with a vector of inputs `input` and get status \
    /// at the end (Accept, Deny or Unfinished) as well as a vector \
    /// of states the DFA went through in order.
    ///
    /// # Example
    /// ```
    /// use finite_state_machine::*;
    ///
    /// // DFA with u16 state IDs and char symbols
    /// let mut dfa: DFA<u16, char> = DFA::new();
    ///
    /// // DFAs input alphabet should be {a, b, c}
    /// let symbols = vec!['a', 'b', 'c'];
    /// dfa.add_symbols(symbols).unwrap();
    ///
    /// // DFA has states 0, 1 and 2
    /// for i in 0..3 {
    ///     dfa.add_state(i).unwrap();
    /// }
    ///
    /// // State 0 is initial state
    /// dfa.set_initial_state(0).unwrap();
    ///
    /// // From state 0 with input 'a', go to state 1
    /// dfa.set_transition((0, 'a'), 1).unwrap();
    ///
    /// // From state 1 with input 'b', go to state 2
    /// dfa.set_transition((1, 'b'), 2).unwrap();
    ///
    /// // Trace run through DFA with input
    /// let result = dfa.trace_run(vec!['a', 'b']);
    /// assert!(result.is_ok());
    ///
    /// // Extract run result and state backtrace from trace run
    /// if let Err(e) = result {
    ///     panic!("{}", e);
    /// } else if let Ok((exit_state, backtrace)) = result {
    ///     assert_eq!(exit_state, RunResult::Unfinished);
    ///     assert_eq!(backtrace, vec![0, 1, 2]);
    /// }
    /// ```
    pub fn trace_run(&mut self, symbols: Vec<SymbolT>) -> Result<(RunResult, Vec<StateIdT>), &str> {
        let mut current_state: StateIdT;

        match self.initial_state {
            None => return Err("DFA without initial state can't be run"),
            Some(state) => current_state = state,
        }

        let mut state_trace = vec![current_state];

        for &symbol in &symbols {
            if self.symbols.contains(&symbol) {
                if let Some(next_state) = self.transitions.get(&(current_state, symbol)) {
                    current_state = *next_state;
                    state_trace.push(current_state);
                } else {
                    return Ok((RunResult::Deny, (*state_trace).to_vec()));
                }
            } else {
                return Err("Input not in DFAs set of symbols.");
            }
        }

        if self.accept_states.contains(&current_state) {
            Ok((RunResult::Accept, (*state_trace).to_vec()))
        } else {
            Ok((RunResult::Unfinished, (*state_trace).to_vec()))
        }
    }
}
