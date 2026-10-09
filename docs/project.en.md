**English** | [繁體中文](project.zh-TW.md) · [Project home](../README.md)

# Project motivation and purpose

This project began with a question motivated by coronary artery calcium scoring: when image intensities undergo small perturbations, what can we guarantee about the resulting score and its category? Threshold-based scoring may appear to involve only a few simple operations, yet it can combine pixel activation, the formation and merging of connected regions, a minimum component-size requirement, and a weight determined by the maximum intensity. Small changes in the input can therefore produce abrupt changes in the output.

This project brings these mechanisms into a precise graph model. It studies the attainable scores and exact extrema within a specified perturbation range, together with the radius and boundary conditions of category invariance. Alongside a finite-state representation, a compression method that preserves the attainable score image, and exact algorithms, the work investigates the computational cost of obtaining these guarantees. In particular, it examines how graph structure, component weights, and size thresholds jointly determine tractability.

The goal is to give threshold-based scoring a precise semantics, independently checkable robustness guarantees, and a clear account of its computational limits. The clinical setting motivates the questions; the conclusions apply to the stated mathematical model and do not constitute clinical validation. The project aims to provide an extensible theoretical foundation for understanding discontinuous methods of image quantification.
