import { gen } from '../src/main.js';

/**
 * This test is useful to check how much coverage
 * trace generation actually gets over the model.
 *
 * yarn jest --collect-coverage
 */
describe('check properties', () => {
  it('_', () => {
    gen(120, true);
    expect(true).toBeTruthy(); // satisfies linter
  });
});
