use core::mem::replace;

use crate::algorithm::selection_functions::SelectionFunction;
use crate::node::{ParentNode, RTreeNode};
use crate::object::RTreeObject;
use crate::params::RTreeParams;
use crate::{Envelope, RTree};

#[cfg(not(test))]
use alloc::{vec, vec::Vec};

#[allow(unused_imports)] // Import is required when building without std
use num_traits::Float;

/// Traversal control returned after visiting a leaf during
/// [`RTree::drain_with_backtracking_visitor`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VisitLeafControl {
    /// Leave this leaf in the tree and continue traversal.
    Keep,
    /// Remove this leaf from the tree and continue traversal.
    Remove,
    /// Remove this leaf and backtrack.
    RemoveAndRevisit,
    /// Leave this leaf in the tree and stop traversal.
    Stop,
}

/// Visitor used by [RTree::drain_with_backtracking_visitor].
pub trait BacktrackingDrainVisitor<T>
where
    T: RTreeObject,
{
    /// Returns `true` if traversal should descend into a parent node.
    ///
    /// This may be called more than once for the same parent, including after
    /// `VisitLeafControl::RemoveAndRevisit` asks traversal to backtrack.
    fn should_unpack_parent(&self, envelope: &T::Envelope) -> bool;

    /// Visits a leaf and decides what traversal should do with it.
    fn visit_leaf(&mut self, leaf: &T) -> VisitLeafControl;

    /// Returns `true` if an already-processed subtree child should be revisited after a leaf
    /// returned `VisitLeafControl::RemoveAndRevisit`.
    ///
    /// The default delegates to [`BacktrackingDrainVisitor::should_unpack_parent`].
    fn should_revisit_parent(&self, envelope: &T::Envelope) -> bool {
        self.should_unpack_parent(envelope)
    }

    /// Returns `true` if an already-processed leaf child should be revisited after a leaf returned
    /// [`VisitLeafControl::RemoveAndRevisit`].
    ///
    /// The default returns `true`.
    fn should_revisit_leaf(&self, _leaf: &T) -> bool {
        true
    }
}

#[derive(Default)]
struct VisitSelectedLeavesOutcome {
    /// Number of leaves removed from this subtree.
    removed: usize,
    /// Whether a descendant returned `VisitLeafControl::RemoveAndRevisit`, so callers must check
    /// already-processed siblings against the visitor's revisit predicates.
    revisit_ancestors: bool,
    /// Whether traversal should stop immediately and unwind without visiting additional siblings.
    stopped: bool,
}

fn first_revisitable_child_index<T, V>(
    visitor: &V,
    node: &ParentNode<T>,
    processed_end: usize,
) -> Option<usize>
where
    T: RTreeObject,
    V: BacktrackingDrainVisitor<T>,
{
    node.children
        .iter()
        .take(processed_end)
        .position(|child| match child {
            RTreeNode::Leaf(leaf) => visitor.should_revisit_leaf(leaf),
            RTreeNode::Parent(parent) => visitor.should_revisit_parent(&parent.envelope),
        })
}

fn visit_selected_leaves_in_place<T, V>(
    node: &mut ParentNode<T>,
    visitor: &mut V,
) -> VisitSelectedLeavesOutcome
where
    T: RTreeObject,
    V: BacktrackingDrainVisitor<T>,
{
    let mut outcome = VisitSelectedLeavesOutcome::default();
    let mut idx = 0;

    while idx < node.children.len() {
        match &mut node.children[idx] {
            RTreeNode::Parent(parent) => {
                if !visitor.should_unpack_parent(&parent.envelope) {
                    idx += 1;
                    continue;
                }

                let child_outcome = visit_selected_leaves_in_place(parent, visitor);
                outcome.removed += child_outcome.removed;
                outcome.revisit_ancestors |= child_outcome.revisit_ancestors;

                if child_outcome.stopped {
                    if outcome.removed != 0 {
                        node.envelope = crate::node::envelope_for_children(&node.children);
                    }
                    outcome.stopped = true;
                    return outcome;
                }

                let child_is_empty = parent.children.is_empty();
                if child_is_empty {
                    node.children.swap_remove(idx);
                }

                if child_outcome.revisit_ancestors {
                    if let Some(revisit_idx) = first_revisitable_child_index(visitor, node, idx) {
                        idx = revisit_idx;
                        continue;
                    }
                }

                if !child_is_empty {
                    idx += 1;
                }
            }
            RTreeNode::Leaf(leaf) => match visitor.visit_leaf(leaf) {
                VisitLeafControl::Keep => {
                    idx += 1;
                }
                VisitLeafControl::Remove => {
                    node.children.swap_remove(idx);
                    outcome.removed += 1;
                }
                VisitLeafControl::RemoveAndRevisit => {
                    node.children.swap_remove(idx);
                    outcome.removed += 1;
                    outcome.revisit_ancestors = true;

                    if let Some(revisit_idx) = first_revisitable_child_index(visitor, node, idx) {
                        idx = revisit_idx;
                    }
                }
                VisitLeafControl::Stop => {
                    if outcome.removed != 0 {
                        node.envelope = crate::node::envelope_for_children(&node.children);
                    }
                    outcome.stopped = true;
                    return outcome;
                }
            },
        }
    }

    if outcome.removed != 0 {
        node.envelope = crate::node::envelope_for_children(&node.children);
    }
    outcome
}

pub(crate) fn drain_with_backtracking_visitor<T, Params, V>(
    rtree: &mut RTree<T, Params>,
    visitor: &mut V,
) -> usize
where
    T: RTreeObject,
    Params: RTreeParams,
    V: BacktrackingDrainVisitor<T>,
{
    if rtree.root().children().is_empty() || !visitor.should_unpack_parent(&rtree.root().envelope) {
        return 0;
    }

    let outcome = visit_selected_leaves_in_place(rtree.root_mut(), visitor);
    *rtree.size_mut() -= outcome.removed;
    outcome.removed
}

/// Iterator returned by `impl IntoIter for RTree`.
///
/// Consumes the whole tree and yields all leaf objects.
pub struct IntoIter<T>
where
    T: RTreeObject,
{
    node_stack: Vec<RTreeNode<T>>,
}

impl<T> IntoIter<T>
where
    T: RTreeObject,
{
    pub(crate) fn new(root: ParentNode<T>) -> Self {
        Self {
            node_stack: vec![RTreeNode::Parent(root)],
        }
    }
}

impl<T> Iterator for IntoIter<T>
where
    T: RTreeObject,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.node_stack.pop() {
            match node {
                RTreeNode::Leaf(object) => return Some(object),
                RTreeNode::Parent(parent) => self.node_stack.extend(parent.children),
            }
        }

        None
    }
}

/// Iterator returned by `RTree::drain_*` methods.
///
/// Draining iterator that removes elements of the tree selected by a
/// [`SelectionFunction`]. Returned by
/// [`RTree::drain_with_selection_function`] and related methods.
///
/// # Remarks
///
/// This iterator is similar to the one returned by `Vec::drain` or
/// `Vec::drain_filter`. Dropping the iterator at any point removes only
/// the yielded values (this behaviour is unlike `Vec::drain_*`). Leaking
/// this iterator leads to a leak amplification where all elements of the
/// tree are leaked.
pub struct DrainIterator<'a, T, R, Params>
where
    T: RTreeObject,
    Params: RTreeParams,
    R: SelectionFunction<T>,
{
    node_stack: Vec<(ParentNode<T>, usize, usize)>,
    removal_function: R,
    rtree: &'a mut RTree<T, Params>,
    original_size: usize,
}

impl<'a, T, R, Params> DrainIterator<'a, T, R, Params>
where
    T: RTreeObject,
    Params: RTreeParams,
    R: SelectionFunction<T>,
{
    pub(crate) fn new(rtree: &'a mut RTree<T, Params>, removal_function: R) -> Self {
        // We replace with a root as a brand new RTree in case the iterator is
        // `mem::forgot`ten.

        // Instead of using `new_with_params`, we avoid an allocation for
        // the normal usage and replace root with an empty `Vec`.
        let root = replace(
            rtree.root_mut(),
            ParentNode {
                children: vec![],
                envelope: Envelope::new_empty(),
            },
        );
        let original_size = replace(rtree.size_mut(), 0);

        let m = Params::MIN_SIZE;
        let max_depth = (original_size as f32).log(m.max(2) as f32).ceil() as usize;
        let mut node_stack = Vec::with_capacity(max_depth);
        node_stack.push((root, 0, 0));

        DrainIterator {
            node_stack,
            original_size,
            removal_function,
            rtree,
        }
    }

    fn pop_node(&mut self, increment_idx: bool) -> Option<(ParentNode<T>, usize)> {
        debug_assert!(!self.node_stack.is_empty());

        let (mut node, _, num_removed) = self.node_stack.pop().unwrap();

        // We only compute envelope for the current node as the parent
        // is taken care of when it is popped.

        // TODO: May be make this a method on `ParentNode`
        if num_removed > 0 {
            node.envelope = crate::node::envelope_for_children(&node.children);
        }

        // If there is no parent, this is the new root node to set back in the rtree
        // O/w, get the new top in stack
        let (parent_node, parent_idx, parent_removed) = match self.node_stack.last_mut() {
            Some(pn) => (&mut pn.0, &mut pn.1, &mut pn.2),
            None => return Some((node, num_removed)),
        };

        // Update the remove count on parent
        *parent_removed += num_removed;

        // If the node has no children, we don't need to add it back to the parent
        if node.children.is_empty() {
            return None;
        }

        // Put the child back (but re-arranged)
        parent_node.children.push(RTreeNode::Parent(node));

        // Swap it with the current item and increment idx.

        // A minor optimization is to avoid the swap in the destructor,
        // where we aren't going to be iterating any more.
        if !increment_idx {
            return None;
        }

        // Note that during iteration, parent_idx may be equal to
        // (previous) children.len(), but this is okay as the swap will be
        // a no-op.
        let parent_len = parent_node.children.len();
        parent_node.children.swap(*parent_idx, parent_len - 1);
        *parent_idx += 1;

        None
    }
}

impl<'a, T, R, Params> Iterator for DrainIterator<'a, T, R, Params>
where
    T: RTreeObject,
    Params: RTreeParams,
    R: SelectionFunction<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        'attempt_loop: loop {
            // Get reference to top node or return None.
            let (node, idx, remove_count) = match self.node_stack.last_mut() {
                Some(node) => (&mut node.0, &mut node.1, &mut node.2),
                None => return None,
            };

            // Try to find a selected item to return.
            if *idx > 0 || self.removal_function.should_unpack_parent(&node.envelope) {
                while *idx < node.children.len() {
                    match &mut node.children[*idx] {
                        RTreeNode::Parent(_) => {
                            // Swap node with last, remove and return the value.
                            // No need to increment idx as something else has replaced it;
                            // or idx == new len, and we'll handle it in the next iteration.
                            let child = match node.children.swap_remove(*idx) {
                                RTreeNode::Leaf(_) => unreachable!("DrainIterator bug!"),
                                RTreeNode::Parent(node) => node,
                            };
                            self.node_stack.push((child, 0, 0));
                            continue 'attempt_loop;
                        }
                        RTreeNode::Leaf(ref leaf) => {
                            if self.removal_function.should_unpack_leaf(leaf) {
                                // Swap node with last, remove and return the value.
                                // No need to increment idx as something else has replaced it;
                                // or idx == new len, and we'll handle it in the next iteration.
                                *remove_count += 1;
                                return match node.children.swap_remove(*idx) {
                                    RTreeNode::Leaf(data) => Some(data),
                                    _ => unreachable!("RemovalIterator bug!"),
                                };
                            }
                            *idx += 1;
                        }
                    }
                }
            }

            // Pop top node and clean-up if done
            if let Some((new_root, total_removed)) = self.pop_node(true) {
                // This happens if we are done with the iteration.
                // Set the root back in rtree and return None
                *self.rtree.root_mut() = new_root;
                *self.rtree.size_mut() = self.original_size - total_removed;
                return None;
            }
        }
    }
}

impl<'a, T, R, Params> Drop for DrainIterator<'a, T, R, Params>
where
    T: RTreeObject,
    Params: RTreeParams,
    R: SelectionFunction<T>,
{
    fn drop(&mut self) {
        // Re-assemble back the original rtree and update envelope as we
        // re-assemble.
        if self.node_stack.is_empty() {
            // The iteration handled everything, nothing to do.
            return;
        }

        loop {
            debug_assert!(!self.node_stack.is_empty());
            if let Some((new_root, total_removed)) = self.pop_node(false) {
                *self.rtree.root_mut() = new_root;
                *self.rtree.size_mut() = self.original_size - total_removed;
                break;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::cell::Cell;
    use std::mem::forget;

    use crate::algorithm::rstar::RStarInsertionStrategy;
    use crate::algorithm::selection_functions::{SelectAllFunc, SelectInEnvelopeFuncIntersecting};
    use crate::point::PointExt;
    use crate::primitives::Line;
    use crate::test_utilities::{create_random_points, create_random_rectangles, SEED_1, SEED_2};
    use crate::AABB;

    use super::*;

    #[test]
    fn test_remove_and_insert() {
        const SIZE: usize = 1000;
        let points = create_random_points(SIZE, SEED_1);
        let later_insertions = create_random_points(SIZE, SEED_2);
        let mut tree = RTree::bulk_load(points.clone());
        for (point_to_remove, point_to_add) in points.iter().zip(later_insertions.iter()) {
            assert!(tree.remove_at_point(point_to_remove).is_some());
            tree.insert(*point_to_add);
        }
        assert_eq!(tree.size(), SIZE);
        assert!(points.iter().all(|p| !tree.contains(p)));
        assert!(later_insertions.iter().all(|p| tree.contains(p)));
        for point in &later_insertions {
            assert!(tree.remove_at_point(point).is_some());
        }
        assert_eq!(tree.size(), 0);
    }

    #[test]
    fn test_remove_and_insert_rectangles() {
        const SIZE: usize = 1000;
        let initial_rectangles = create_random_rectangles(SIZE, SEED_1);
        let new_rectangles = create_random_rectangles(SIZE, SEED_2);
        let mut tree = RTree::bulk_load(initial_rectangles.clone());

        for (rectangle_to_remove, rectangle_to_add) in
            initial_rectangles.iter().zip(new_rectangles.iter())
        {
            assert!(tree.remove(rectangle_to_remove).is_some());
            tree.insert(*rectangle_to_add);
        }
        assert_eq!(tree.size(), SIZE);
        assert!(initial_rectangles.iter().all(|p| !tree.contains(p)));
        assert!(new_rectangles.iter().all(|p| tree.contains(p)));
        for rectangle in &new_rectangles {
            assert!(tree.contains(rectangle));
        }
        for rectangle in &initial_rectangles {
            assert!(!tree.contains(rectangle));
        }
        for rectangle in &new_rectangles {
            assert!(tree.remove(rectangle).is_some());
        }
        assert_eq!(tree.size(), 0);
    }

    #[test]
    fn test_remove_at_point() {
        let points = create_random_points(1000, SEED_1);
        let mut tree = RTree::bulk_load(points.clone());
        for point in &points {
            let size_before_removal = tree.size();
            assert!(tree.remove_at_point(point).is_some());
            assert!(tree.remove_at_point(&[1000.0, 1000.0]).is_none());
            assert_eq!(size_before_removal - 1, tree.size());
        }
    }

    #[test]
    fn test_remove() {
        let points = create_random_points(1000, SEED_1);
        let offsets = create_random_points(1000, SEED_2);
        let scaled = offsets.iter().map(|p| p.mul(0.05));
        let edges: Vec<_> = points
            .iter()
            .zip(scaled)
            .map(|(from, offset)| Line::new(*from, from.add(&offset)))
            .collect();
        let mut tree = RTree::bulk_load(edges.clone());
        for edge in &edges {
            let size_before_removal = tree.size();
            assert!(tree.remove(edge).is_some());
            assert!(tree.remove(edge).is_none());
            assert_eq!(size_before_removal - 1, tree.size());
        }
    }

    #[test]
    fn test_drain_iterator() {
        const SIZE: usize = 1000;
        let points = create_random_points(SIZE, SEED_1);
        let mut tree = RTree::bulk_load(points);

        let drain_count = DrainIterator::new(&mut tree, SelectAllFunc)
            .take(250)
            .count();
        assert_eq!(drain_count, 250);
        assert_eq!(tree.size(), 750);

        let drain_count = DrainIterator::new(&mut tree, SelectAllFunc)
            .take(250)
            .count();
        assert_eq!(drain_count, 250);
        assert_eq!(tree.size(), 500);

        // Test Drain forget soundness
        forget(DrainIterator::new(&mut tree, SelectAllFunc));
        // Check tree has no nodes
        // Tests below will check the same tree can be used again
        assert_eq!(tree.size(), 0);

        let points = create_random_points(1000, SEED_1);
        points.into_iter().for_each(|pt| tree.insert(pt));

        // The total for this is 406 (for SEED_1)
        let env = AABB::from_corners([-2., -0.6], [0.5, 0.85]);

        let sel = SelectInEnvelopeFuncIntersecting::new(env);
        let drain_count = DrainIterator::new(&mut tree, sel).take(80).count();
        assert_eq!(drain_count, 80);

        let sel = SelectInEnvelopeFuncIntersecting::new(env);
        let drain_count = DrainIterator::new(&mut tree, sel).count();
        assert_eq!(drain_count, 326);

        let sel = SelectInEnvelopeFuncIntersecting::new(env);
        let sel_count = tree.locate_with_selection_function(sel).count();
        assert_eq!(sel_count, 0);
        assert_eq!(tree.size(), 1000 - 80 - 326);
    }

    #[test]
    fn test_drain_visitor_stop_keeps_current_leaf_and_stops() {
        struct StopAtFirstLeaf {
            visited: bool,
        }

        impl BacktrackingDrainVisitor<[i32; 2]> for StopAtFirstLeaf {
            fn should_unpack_parent(&self, _: &AABB<[i32; 2]>) -> bool {
                true
            }

            fn visit_leaf(&mut self, _: &[i32; 2]) -> VisitLeafControl {
                assert!(!self.visited);
                self.visited = true;
                VisitLeafControl::Stop
            }
        }

        let mut tree = RTree::bulk_load(vec![[0, 0], [1, 0]]);
        let mut visitor = StopAtFirstLeaf { visited: false };
        let removed = tree.drain_with_backtracking_visitor(&mut visitor);

        assert!(visitor.visited);
        assert_eq!(removed, 0);
        assert_eq!(tree.size(), 2);
        assert!(tree.contains(&[0, 0]));
        assert!(tree.contains(&[1, 0]));
    }

    #[test]
    fn test_drain_visitor_remove_and_revisit_respects_revisit_predicate() {
        struct DeclineRevisitOfFirstSeen {
            first_seen: Cell<Option<[i32; 2]>>,
            select_first_seen: bool,
        }

        impl BacktrackingDrainVisitor<[i32; 2]> for DeclineRevisitOfFirstSeen {
            fn should_unpack_parent(&self, _: &AABB<[i32; 2]>) -> bool {
                true
            }

            fn visit_leaf(&mut self, point: &[i32; 2]) -> VisitLeafControl {
                if self.select_first_seen {
                    if self.first_seen.get() == Some(*point) {
                        return VisitLeafControl::Remove;
                    }
                    return VisitLeafControl::Keep;
                }

                if self.first_seen.get().is_none() {
                    self.first_seen.set(Some(*point));
                    return VisitLeafControl::Keep;
                }

                assert_ne!(self.first_seen.get(), Some(*point));
                self.select_first_seen = true;
                VisitLeafControl::RemoveAndRevisit
            }

            fn should_revisit_leaf(&self, _: &[i32; 2]) -> bool {
                false
            }
        }

        let mut tree = RTree::bulk_load(vec![[0, 0], [1, 0]]);
        let mut visitor = DeclineRevisitOfFirstSeen {
            first_seen: Cell::new(None),
            select_first_seen: false,
        };
        let removed = tree.drain_with_backtracking_visitor(&mut visitor);
        let first_seen = visitor.first_seen.get().unwrap();

        assert_eq!(removed, 1);
        assert_eq!(tree.size(), 1);
        assert!(tree.contains(&first_seen));
    }

    #[test]
    fn test_into_iter() {
        const SIZE: usize = 100;
        let mut points = create_random_points(SIZE, SEED_1);
        let tree = RTree::bulk_load(points.clone());

        let mut vec = tree.into_iter().collect::<Vec<_>>();

        assert_eq!(vec.len(), points.len());

        points.sort_unstable_by(|lhs, rhs| lhs.partial_cmp(rhs).unwrap());
        vec.sort_unstable_by(|lhs, rhs| lhs.partial_cmp(rhs).unwrap());

        assert_eq!(points, vec);
    }
}
