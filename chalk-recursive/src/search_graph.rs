use std::ops::Add;
use std::ops::Index;
use std::ops::IndexMut;
use std::usize;

use super::stack::StackDepth;
use crate::{Minimums, UCanonicalGoal};
use chalk_ir::{interner::Interner, ClausePriority, Fallible, NoSolution};
use chalk_solve::Solution;
use rustc_hash::FxHashMap;
use tracing::{debug, instrument};

/// The "search graph" stores in-progress goals that are still
/// being solved.
pub(super) struct SearchGraph<I: Interner> {
    indices: FxHashMap<UCanonicalGoal<I>, DepthFirstNumber>,
    nodes: Vec<Node<I>>,
}

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(super) struct DepthFirstNumber {
    index: usize,
}

pub(super) struct Node<I: Interner> {
    pub(crate) goal: UCanonicalGoal<I>,

    pub(crate) solution: Fallible<Solution<I>>,
    pub(crate) solution_priority: ClausePriority,

    /// This is `Some(X)` if we are actively exploring this node, or
    /// `None` otherwise.
    pub(crate) stack_depth: Option<StackDepth>,

    /// While this node is on the stack, this field will be set to
    /// contain our own depth-first number. Once the node is popped
    /// from the stack, it contains the DFN of the minimal ancestor
    /// that the table reached (or MAX if no cycle was encountered).
    pub(crate) links: Minimums,

    /// If this is true, the node is the start of coinductive cycle.
    /// Thus, some cleanup has to be done before its result can be
    /// cached to rule out false positives.
    pub(crate) coinductive_start: bool,
}

impl<I: Interner> SearchGraph<I> {
    pub(crate) fn new() -> Self {
        SearchGraph {
            indices: FxHashMap::default(),
            nodes: vec![],
        }
    }

    pub(crate) fn lookup(&self, goal: &UCanonicalGoal<I>) -> Option<DepthFirstNumber> {
        self.indices.get(goal).cloned()
    }

    /// Insert a new search node in the tree. The node will be in the initial
    /// state for a search node:
    ///
    /// - stack depth as given
    /// - links set to its own DFN
    /// - solution is initially `NoSolution`
    pub(crate) fn insert(
        &mut self,
        goal: &UCanonicalGoal<I>,
        stack_depth: StackDepth,
    ) -> DepthFirstNumber {
        let dfn = DepthFirstNumber {
            index: self.nodes.len(),
        };
        let node = Node {
            goal: goal.clone(),
            solution: Err(NoSolution),
            solution_priority: ClausePriority::High,
            stack_depth: Some(stack_depth),
            links: Minimums { positive: dfn },
            coinductive_start: false,
        };
        self.nodes.push(node);
        let previous_index = self.indices.insert(goal.clone(), dfn);
        assert!(previous_index.is_none());
        dfn
    }

    /// Clears all nodes with a depth-first number greater than or equal `dfn`.
    #[instrument(level = "debug", skip(self))]
    pub(crate) fn rollback_to(&mut self, dfn: DepthFirstNumber) {
        self.indices.retain(|_key, value| *value < dfn);
        self.nodes.truncate(dfn.index);
    }

    /// Removes all nodes with a depth-first-number greater than or
    /// equal to `dfn`, adding their final solutions into the cache.
    #[instrument(level = "debug", skip(self))]
    pub(crate) fn move_to_cache(
        &mut self,
        dfn: DepthFirstNumber,
        cache: &mut FxHashMap<UCanonicalGoal<I>, Fallible<Solution<I>>>,
    ) {
        self.indices.retain(|_key, value| *value < dfn);
        for node in self.nodes.drain(dfn.index..) {
            assert!(node.stack_depth.is_none());
            assert!(node.links.positive >= dfn);
            debug!("caching solution {:#?} for {:#?}", node.solution, node.goal);
            cache.insert(node.goal, node.solution);
        }
    }

    /// Removes all nodes that are part of a coinductive cycle and
    /// have a solution as they might be false positives due to
    /// coinductive reasoning.
    #[instrument(level = "debug", skip(self))]
    pub(crate) fn remove_false_positives_after(&mut self, dfn: DepthFirstNumber) {
        let mut false_positive_indices = vec![];

        // Find all possible false positives in the graph below the
        // start of the coinductive cycle
        for (index, node) in self.nodes[dfn.index + 1..].iter().enumerate() {
            if node.solution.is_ok() {
                false_positive_indices.push(index + dfn.index + 1);
            }
        }

        // Remove the potential false positives from the indices
        self.indices
            .retain(|_key, value| !false_positive_indices.contains(&value.index));

        // Remove the potential false positives from the nodes
        // in descending order to avoid unnecessary shifts
        for false_positive_index in false_positive_indices.into_iter().rev() {
            self.nodes.remove(false_positive_index);
        }
    }
}

impl<I: Interner> Index<DepthFirstNumber> for SearchGraph<I> {
    type Output = Node<I>;

    fn index(&self, table_index: DepthFirstNumber) -> &Node<I> {
        &self.nodes[table_index.index]
    }
}

impl<I: Interner> IndexMut<DepthFirstNumber> for SearchGraph<I> {
    fn index_mut(&mut self, table_index: DepthFirstNumber) -> &mut Node<I> {
        &mut self.nodes[table_index.index]
    }
}

impl DepthFirstNumber {
    pub(crate) const MAX: DepthFirstNumber = DepthFirstNumber { index: usize::MAX };
}

impl Add<usize> for DepthFirstNumber {
    type Output = DepthFirstNumber;

    fn add(self, v: usize) -> DepthFirstNumber {
        DepthFirstNumber {
            index: self.index + v,
        }
    }
}
