//! # Automatastic
//!
//! Model deterministic finite automata as a Type ```Automaton```,
//! encapsulating the Tuple (Q, q_0, Sigma, F, Delta):
//! - The finite set of states (Q) ```states```,
//! - The initial state (q_0) ```initial_state```,
//! - The finite set of input symbols (Sigma) ```symbols```,
//! - The set of accept states (F) ```accept_states```,
//! - The transition functions (Delta) ```transitions```,
//!   defined in terms of a state and an input symbol.

use std::result::Result;
use std::hash::Hash;
use fnv::FnvHashMap;
use fnv::FnvHashSet;

#[derive(Debug)]
pub struct DFA<StateIdT, SymbolT> {
    pub states: FnvHashSet<StateIdT>,
    pub initial_state: Option<StateIdT>,
    pub symbols: FnvHashSet<SymbolT>,
    pub accept_states: FnvHashSet<StateIdT>,
    pub transitions: FnvHashMap<(StateIdT, SymbolT), StateIdT>,
}

#[derive(Debug, PartialEq)]
pub enum RunResult {
    Accept,
    Deny,
    Unfinished,
}

impl<StateIdT, SymbolT> DFA<StateIdT, SymbolT>
where
StateIdT: Hash + Eq + Copy,
SymbolT: Hash + Eq + Copy
{

    /// Add a state to a DFAs set of states.
    ///
    /// # Example
    /// ```
    /// // DFA with u16 state IDs and u16 symbols
    /// let mut dfa: finite_state_machine::DFA<u16, u16>;
    ///
    /// dfa = finite_state_machine::DFA {
    ///     states: fnv::FnvHashSet::default(),
    ///     initial_state: None,
    ///     symbols: fnv::FnvHashSet::default(),
    ///     accept_states: fnv::FnvHashSet::default(),
    ///     transitions: fnv::FnvHashMap::default(),
    /// };
    ///
    /// // Add a new state with ID 0:
    /// assert!(dfa.add_state(0).is_ok());
    ///
    /// // Try to add state that already exists:
    /// assert!(dfa.add_state(0).is_err());
    /// ```
    pub fn add_state(self: &mut DFA<StateIdT, SymbolT>, state: StateIdT) -> Result<(), &str> {
        if !self.states.contains(&state) {
            self.states.insert(state);
            Ok(())
        } else {
            Err("State with given ID is already present in set of states.")
        }
    }

    pub fn add_symbols(self: &mut DFA<StateIdT, SymbolT>, symbols: Vec<SymbolT>) -> () {
        for &symbol in &symbols {
            if !self.symbols.contains(&symbol) {
                self.symbols.insert(symbol);
            }
        }
    }

    pub fn add_transition(self: &mut DFA<StateIdT, SymbolT>, input: (StateIdT, SymbolT), result_state: StateIdT) -> () {
        if !self.transitions.contains_key(&input) {
            self.transitions.insert(input, result_state);
        } else {
            panic!(
                "Transition from given state with given symbol already present in set of transitions. \
                The type DFA does not support non-deterministic automata."
            );
        }
    }

    pub fn declare_accept_state(self: &mut DFA<StateIdT, SymbolT>, state: StateIdT) -> () {
        if self.states.contains(&state) {
            if !self.accept_states.contains(&state) {
                self.accept_states.insert(state);
            }
        } else {
            panic!("State that is not part of DFA can't be declared as an accept state.");
        }
    }

    pub fn set_initial_state(self: &mut DFA<StateIdT, SymbolT>, state: StateIdT) -> () {
        self.initial_state = Some(state);
    }

    pub fn trace_run(self: &DFA<StateIdT, SymbolT>, input: Vec<SymbolT>) -> Result<(RunResult, Vec<StateIdT>), &str> {

        let mut current_state: StateIdT;

        match self.initial_state {
            None => return Err("DFA without initial state can't be run"),
            Some(state) => current_state = state,
        }

        let mut state_trace = vec![current_state];

        if input.is_empty() {
            if self.accept_states.contains(&current_state) {
                return Ok((RunResult::Accept, (*state_trace).to_vec()));
            } else {
                return Ok((RunResult::Deny, (*state_trace).to_vec()));
            }
        }
        
        for &symbol in &input {
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
            return Ok((RunResult::Accept, (*state_trace).to_vec()));
        } else {
            return Ok((RunResult::Deny, (*state_trace).to_vec()));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trace_run_works() {
        let mut dfa: DFA<u16, u16> = DFA {
            states: FnvHashSet::default(),
            initial_state: None,
            symbols: FnvHashSet::default(),
            accept_states: FnvHashSet::default(),
            transitions: FnvHashMap::default(),
        };

        let mut symbols: Vec<u16> = Vec::new();
        for i in 0..10 {
            symbols.push(i);
        }

        dfa.add_symbols(symbols);

        for i in 0..3 {
            match dfa.add_state(i) {
                Ok(_) => continue,
                Err(_) => return,
            }
        }

        dfa.set_initial_state(0);
        dfa.declare_accept_state(2);

        dfa.add_transition((0, 5), 1);
        dfa.add_transition((1, 5), 2);

        let input: Vec<u16> = vec![5, 5];
        let output = dfa.trace_run(input);
        let result = output.unwrap();

        assert_eq!(result, (RunResult::Accept, vec![0,1,2]));

        // only [0-9] are valid symbols, 10 is invalid.
        let input: Vec<u16> = vec![5, 10];
        let output = dfa.trace_run(input);
        let result = match output {
            Ok(_)  => Ok(()),
            Err(_) => Err(()),
        };

        assert!(result.is_err());
    }
}

