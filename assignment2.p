%------------------------------------------------------------------------------
% Food chains in typed first-order logic (TFF)
% One file containing all axioms and conjectures in the given order.
%------------------------------------------------------------------------------

%-------------------- Types --------------------

tff(species_type,  type, species:   $tType).
tff(foodlink_type, type, foodlink:  $tType).
tff(foodchain_type,type, foodchain: $tType).

%-------------------- Symbols --------------------

tff(eats_type,     type, eats:      (species * species) > $o).
tff(eaten_type,    type, eaten:     foodlink > species).
tff(eater_type,    type, eater:     foodlink > species).

tff(primary_type,  type, primary_producer: species > $o).
tff(apex_type,     type, apex_predator:    species > $o).

tff(chain_type,    type, food_chain: (foodchain * species * species) > $o).
tff(shorter_type,  type, shorter_by_one: (foodchain * foodchain) > $o).

tff(complete_type, type, complete_chain: (foodchain * species * species) > $o).

tff(depends_type,  type, depends_on: (species * species) > $o).

%------------------------------------------------------------------------------
% Axiom: The eater of a food link eats the eaten of the link.
%------------------------------------------------------------------------------

tff(ax_link_eats,axiom,
    ! [L:foodlink] :
      eats(eater(L), eaten(L)) ).

%------------------------------------------------------------------------------
% Axiom: The eaten and eater of a food link are not the same (no cannibalism).
%------------------------------------------------------------------------------

tff(ax_no_cannibalism,axiom,
    ! [L:foodlink] :
      eater(L) != eaten(L) ).

%------------------------------------------------------------------------------
% Axiom: Every species eats something or is eaten by something (or both).
%------------------------------------------------------------------------------

tff(ax_every_species_related,axiom,
    ! [X:species] :
      ( (? [Y:species] : eats(X,Y))
      | (? [Y:species] : eats(Y,X)) ) ).

%------------------------------------------------------------------------------
% Axiom: Something is a primary producer iff it eats no other species.
%------------------------------------------------------------------------------

tff(ax_primary_iff_eats_none,axiom,
    ! [X:species] :
      ( primary_producer(X)
    <=> ~ (? [Y:species] : eats(X,Y)) ) ).

%------------------------------------------------------------------------------
% Theorem: If something is a primary producer then there is no food link such
%          that the primary producer is the eater of the food link.
%------------------------------------------------------------------------------

tff(thm_primary_no_outgoing_link,conjecture,
    ! [P:species] :
      ( primary_producer(P)
     => ~ (? [L:foodlink] : eater(L) = P) ) ).

%------------------------------------------------------------------------------
% Theorem: Every primary producer is eaten by some other species.
%------------------------------------------------------------------------------

tff(thm_primary_is_eaten,conjecture,
    ! [P:species] :
      ( primary_producer(P)
     => ? [S:species] : eats(S,P) ) ).

%------------------------------------------------------------------------------
% Theorem: If a species is not a primary producer then there is another species
%          that it eats.
%------------------------------------------------------------------------------

tff(thm_not_primary_eats_someone,conjecture,
    ! [X:species] :
      ( ~ primary_producer(X)
     => ? [Y:species] : eats(X,Y) ) ).

%------------------------------------------------------------------------------
% Axiom: Something is an apex predator iff there is no species that eats it.
%------------------------------------------------------------------------------

tff(ax_apex_iff_not_eaten,axiom,
    ! [X:species] :
      ( apex_predator(X)
    <=> ~ (? [Y:species] : eats(Y,X)) ) ).

%------------------------------------------------------------------------------
% Theorem: If something is an apex predator then there is no food link such
%          that the apex predator is the eaten of the food link.
%------------------------------------------------------------------------------

tff(thm_apex_no_incoming_link,conjecture,
    ! [A:species] :
      ( apex_predator(A)
     => ~ (? [L:foodlink] : eaten(L) = A) ) ).

%------------------------------------------------------------------------------
% Theorem: Every apex predator eats some other species.
%------------------------------------------------------------------------------

tff(thm_apex_eats_someone,conjecture,
    ! [A:species] :
      ( apex_predator(A)
     => ? [Y:species] : eats(A,Y) ) ).

%------------------------------------------------------------------------------
% Theorem: If a species is not an apex predator then there is another species
%          that eats it.
%------------------------------------------------------------------------------

tff(thm_not_apex_is_eaten,conjecture,
    ! [X:species] :
      ( ~ apex_predator(X)
     => ? [Y:species] : eats(Y,X) ) ).

%------------------------------------------------------------------------------
% Axiom: For every food chain, the start of the chain is the eaten of some food
% link, and one of the following holds:
% (i)  the eater of the food link is the end of the food chain, xor
% (ii) there is a shorter food chain (shorter by one food link) from the eater
%      of the food link to the end of the whole food chain.
%------------------------------------------------------------------------------

tff(ax_chain_step,axiom,
    ! [C:foodchain, S:species, E:species] :
      ( food_chain(C,S,E)
     => ? [L:foodlink] :
          ( eaten(L) = S
          & ( (eater(L) = E)
            <~>
            ? [C2:foodchain] :
              ( shorter_by_one(C2,C)
              & food_chain(C2, eater(L), E) ) ) ) ) ).

%------------------------------------------------------------------------------
% Axiom: There is no food chain from a species back to itself (no death spirals).
%------------------------------------------------------------------------------

tff(ax_no_cycle_chain,axiom,
    ! [X:species] :
      ~ (? [C:foodchain] : food_chain(C,X,X)) ).

%------------------------------------------------------------------------------
% Axiom: A complete food chain starts at a primary producer, and ends at an apex
% predator.
%------------------------------------------------------------------------------

tff(ax_complete_chain_def,axiom,
    ! [C:foodchain, S:species, E:species] :
      ( complete_chain(C,S,E)
    <=> ( food_chain(C,S,E)
        & primary_producer(S)
        & apex_predator(E) ) ) ).

%------------------------------------------------------------------------------
% Axiom: Every species is in some complete food chain, i.e.,
% (i)  the species is the primary producer start of the complete food chain, or
% (ii) the species is the apex predator at the end of the complete food chain, or
% (iii) there is a non-complete food chain from the start of the complete food
%       chain to the species, and another non-complete food chain from the species
%       to the end of the complete food chain.
%------------------------------------------------------------------------------

tff(ax_every_species_in_some_complete_chain,axiom,
    ! [X:species] :
      ? [C:foodchain, S:species, E:species] :
        ( complete_chain(C,S,E)
        & ( X = S
          | X = E
          | ? [C1:foodchain, C2:foodchain] :
              ( food_chain(C1,S,X)
              & food_chain(C2,X,E)
              & ~ complete_chain(C1,S,X)
              & ~ complete_chain(C2,X,E) ) ) ) ).

%------------------------------------------------------------------------------
% Theorem: The start species of a complete food chain does not eat the end species.
%------------------------------------------------------------------------------

tff(thm_complete_start_not_eat_end,conjecture,
    ! [C:foodchain, S:species, E:species] :
      ( complete_chain(C,S,E)
     => ~ eats(S,E) ) ).

%------------------------------------------------------------------------------
% Theorem: If a species is neither a primary producer nor an apex predator, then
% there is a food chain from a primary producer to that species, and another food
% chain from that species to an apex predator.
%------------------------------------------------------------------------------

tff(thm_middle_has_chains_to_and_from,conjecture,
    ! [X:species] :
      ( (~ primary_producer(X) & ~ apex_predator(X))
     => ? [P:species, A:species, C1:foodchain, C2:foodchain] :
          ( primary_producer(P)
          & apex_predator(A)
          & food_chain(C1,P,X)
          & food_chain(C2,X,A) ) ) ).

%------------------------------------------------------------------------------
% Axiom: Given two species, the first depends on the second iff there is a food
% chain from the second to the first.
%------------------------------------------------------------------------------

tff(ax_depends_iff_chain,axiom,
    ! [X:species, Y:species] :
      ( depends_on(X,Y)
    <=> ? [C:foodchain] : food_chain(C,Y,X) ) ).

%------------------------------------------------------------------------------
% Theorem: If a species is not an apex predator then there is an apex predator
% that depends on the species.
%------------------------------------------------------------------------------

tff(thm_non_apex_has_apex_depending,conjecture,
    ! [X:species] :
      ( ~ apex_predator(X)
     => ? [A:species] :
          ( apex_predator(A)
          & depends_on(A,X) ) ) ).

%------------------------------------------------------------------------------
% Theorem: An apex predator depends on all primary producers of all complete food
% chains that end at the apex predator.
%------------------------------------------------------------------------------

tff(thm_apex_depends_on_all_chain_starts,conjecture,
    ! [A:species, P:species, C:foodchain] :
      ( ( complete_chain(C,P,A) )
     => depends_on(A,P) ) ).

%------------------------------------------------------------------------------
