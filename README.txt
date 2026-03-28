Revision historic changes

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.5
    * Working scroll bars for both areas

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.5.1
    * Results area and Logging Events areas are now dynamically resizable

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.5.2
    * Files Selection now is taken from a List Box, default is all files selected, can select one or multiple files to work on
    * Added option for printing whole file contents in results area, and synced search_files function to work with this

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.6
    Replace most of the on-screen buttons for a menu bar and working hot-keys for intuitive functioning
    Implemented a "find" dialog that gathers find variants + options
    
    bug fixes and corrections
        - corrected the "files processed" number shown, used (i+1) instead of len(files_selected)
        - corrected the widgets frames (completed them with self.x)
        - adjusted progress bar to a thinner size for allowing more space for text and log areas
        - added a local variable for keeping same files in case recalling askopenfiles method and not selecting anything
        - place cursor in entry field upon opening find dialog (focus)
-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.7
    Added ability to add up more files from same or any other path while ensuring no duplicates are created
    Added ability to remove files from the list while keeping 1-to-1 mapping between file paths (for background processing) 
        and file names (for cleaner UI display)
    Added tooltip help when hovering over the file names listed to show their whole file paths
    
    bug fixes and corrections
        removed 'create_widgets' unused function
        removed unused imports and line(s) commented out
        
-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.8    
    Added accelerator CTRL + P for printing file contents, along with selectable option from File Menu, and Icons for all menu actions
    Included regex validation for searching strings and enabled catching of errors related
    Removed closure of find dialog whenever is pressed find in files or find in text area buttons (not an error but a way of handling it)

    bug fixes and corrections
        corrected the warning message info and size that appeared trimmed when no file selected to be printed
        corrected the issue of not handling correctly two files with the same name of different paths
        corrected the issue of Select/Deselect files button not showing Label accordingly upon removing files
        corrected the "Find" simple function

-----------------------------------------------------------------------------------------------------------------------------------------------    
ver. 0.9
    Implemented the Decode Dmesg functionality via right click context menu option and creates a duplicate of the original file but added decoded entries per line
        Working modules:
            Decode Responses (using json file)
            Decode Admin GLP
    
    bug fixes and corrections
        corrected the issue of files being deselected when user double clicks on search entry field or goes back to it via TAB key

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.1
    Added context menu opening by pressing context menu from keyboard, andcontext menu will open at the right side of the file name
        and not on mouse pointer position. Also set focus to list of files when updating the listbox element
    Added coverage for Vendor Specific Opcodes and LIDs
    Combined LPOL + LPOU
    
    bug fixes and corrections
        set UTF-8 encoding when reading the dmesg to prevent failing due to reading special characters

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.2
    Added functions for decoding Admin commands: 06h, 09h, 0Ah, 0Dh, 10h, 11h, 14h, 80h, 84h
    set 'decode_csi' function separately from 'get log page' so that it can be called by more functions that uses csi field
    
    bug fixes and corrections
        corrected logic inside 'show_context_menu' for it to show the context menu accordingly depending on the way of calling it: keyboard or mouse

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.3
    Added functions for decoding Admin commands: 00h, 01h, 04h, 05h, 08h, 0Ch, 15h, 19h, 1Ah, 1Ch
    
    bug fixes and corrections
        corrected duplicated Int casting for some values inside commands decoding functions

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.4
    Modified the Find functionality to allow Reverse search, button text changes to Find Next, match counts are reflected
    Added Find All functionality along with Debuggability module; inherently Modified the Find dialog section and applied a rearranged layout for better readability
    Modified Vertical Scrollbar section to work on highlighting process from Find All function
    Changed "Find in text area" button text to "Filter Matches"

    bug fixes and corrections
        corrected log message "Search Cancelled by User" when pressing CTRL + C and no active search

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.5
    Refactored the Find All function as it was lasting like forever to finish while working with giant files; bottlenecks spotted in both Search and Highlight phases
    included content update dedicated functions to aid printing of files logic
    bug fixes and corrections

    bug fixes and corrections
        removed unnecessary on_motion function

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.6
    Re-arranged function locations so that the code is now organized into specific sections
    improved Dark mode (not widely tested)
    included function create_widgets()
    Added Clear screen option in newly created Edit menu
    created update_match_count() function so that other functions can Implement it
    
    bug fixes and corrections
        Corrected:  Error reading text area: name 'lines' is not defined when searching for a term, and hitting Filter Matches

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.7
    Implemented Find Next: keep searching/navigating thru the document shown by keep pressing "Find" button (which turns into "Find Next" now)
    Implememted Reverse Find functionality (only for normal text searches, regex is not recommended/supported)
    Using now separate highlight tags for Find and Find All so that they can coexist
    Added Find All counts into Matches count Label

    bug fixes and corrections
        Corrected: Find is re-scanning all text every time, need to be ultra-efficient for working with gigantinc files
        Corrected: When pressing CTRL + C for copying some text it's shown the the message "search cancelled", but no actual search is in progress

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.8
    Simplified the event logged when a term is found, to show only total time spend during whole search process and used comma-separator

    bug fixes and corrections
        Corrected: do not allow to open more than one Find dialog window

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.8.1
    Created a _ui_poller() for processing queued UI actions from worker threads (runs in main thread).
    Reformatted find_all_terms, start_search and search_files functions to be Thread-safe 

    bug fixes and corrections
        Corrected - the preferred method to open the app is on secondary display, but it'll break the logic when having only one display.
        Corrected - having text loaded, pressing CTRL + O will trigger a newline insertion upon opening a new File browsing dialog
        Corrected - removed duplicated methods: on_close and decode_dmesg

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.8.2
    Changed cancellation shortcut key to CTRL + SHIFT + C to prevent conflicting with regular Copy key combo
    Suppressed the "Highlight results" for now, as its functionality is already covered by Find All 
    Included message logged for Find All as well as a pop-up message when nothing is found, same as with regular Find
    Make visible the first term found when searching thru Find All

    bug fixes and corrections
        Removed redundant cancellation message for search_files; showing only the detailed message instead of the generic one

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 0.9.9
    Find dialog now uses Tabs methodology (ttk.Notebook) to make room for RCV tab which is focused and independent of regular Find functionality
    Improved _ui_poller function's conditions

    bug fixes and corrections
        Corrected - cancellation event messages were sometimes duplicated, hence redundant

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.0
    implemented double-click token selection + triple-click line selection
    implemented context menu with: Cut/Copy/Paste + Undo/Redo + Highlight tools (including clear highlight for find/find all tags)
    implemented Status bar (Lines, cursor coordinates, selected) + line-number gutter updates
    implemented token selection and navigation via CTRL + SHIFT + Left/Right arrow keys
    implemented Command-mode search in RCV Find tab
    integrated SCT & SC disctionary into main code to avoid external dependency
    implemented double-click to print a file from listbox
    implemented multi-file selection using PgDn/PgUp keys

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.1
    implemented file size - per file into listbox and total selected file size in a label
    implemented safety guardrails for large file loads, to prevent app going unresponsive while handling large buffers
    implemented guard for Find All as well, since it copies the full buffer 
    implemented highlight nearby occurrences of the selected token while double-clicking token selection + substring highlight
    re-arranged buttons and labels for better visual-looking, and added new Clear Text button
    changed 'select all' files when loading new files to the listbox, and moved to 'select latest only' behavior
    
    bug fixes and corrections
        corrected sporadic issue that had duplicated line numbers
        implemented gutter dynamyc growth and considers max 9-digit numbers for huge buffer loads
        implemented Recreation of the result Text widgets (fast clear) to avoid long stalls on huge buffers

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.2
    implemented confirmation message to prevent accidental app closing

    bug fixes and corrections
        fixed RCV Command Search issue: doing searches on only ~60-70 MB buffers lasting forever; moved to one-pass line mapping instead of per-match bisect
        fixed progress bar animation rolling back to 0 on RCV searches AND while cancelling a search

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.3
    implemented tabbed workspace with functionality for opening separate files and core functionalities:
        a) open new blank files (ctrl + N)
        b) open files loaded from listbox (double-click)
        c) navigate thru tabs (ctrl + PgUp/Dn)
        d) save changes (ctrl + S)
        e) close current tab (ctrl + W and context menu option and "X" icon)
        f) close all tabs (ctrl + shift + W and button added)

        notes: 
        1- besides of key combo shortcuts, added options to menu bar
        2- results tab remains always-open, for dumping filtered searches
        3- gutter & footer status bar refreshing per tab

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.4
    implemented  Pin Tab functionality via context menu. While a Tab is pinned it cannot be closed when a Close All Tabs action is invoked.
    refactored the portion of code that does the decoding of the SCT & SC responses, so that it caches the mapping to avoid rebuild the dict on every call
    added Tab tooltip for when user hovers over a tab's name to show the full file's path
    standardized try-except blocks via _try() helper that also logs when DEBUG is on    
    made the active tab to show differentiated againnt the unactive tabs aligned to the same violet tone seen in other elements; menu items and tabs from Find dialog were also aligned to this theme
    implemented switching focus to Results Tab upon finding matches when doing searches with Find in Files, Filter Matches and RCV searches that do not have "Save to file" option checked

    bug fixes and corrections
        corrected progress bar animation rolling back to '0' upon decode dmesg completion, instead of immediate 100% -> 0 % when finishing
        corrected decode dmesg completion time shown in events logger, as it was inaccurate
        removed highlight option for find dialog, no more needed since all highligh handling implemented in the past via Find, Find All, Context menu -> highlight
        relocated monitor detection to main() for code hygiene, i.e. move away from imports
        corrected highlights and context menu not working on tabs different than Results tab
        corrected Find All highlights not repainting when scrolling in Tabs
        corrected Ctrl+O inserting a newline in Tabs
        
-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.5
    implemented multi-tab opening at once when selecting multiple files from listbox, accessible thru both context menu and Ctrl+Shift+P key combo
    included "Tabs open" counts label, as well as common editing options to Edit menu, and added a few more highlight coloring options, for convenience and better UX

    bug fixes and corrections
        corrected issue of Results tab not refreshing when printing multiple files while triggering Print action from a different tab than Results tab, and printing inside the individual tab instead
        corrected no warning popup shown when pressing Ctrl+Shift+W key combo; standardized it to align to the action called by the "Close all Tabs" button
        corrected issue of not showing file name newly created from an Untitled tab, and get it to show its full path when hovering over, and made it accessible in listbox
        corrected issue of not switchng caret when creating a new file and focus moved to it for editing, thus causing modifications to the wrong file 
        corrected issue for Undo action that was causing the entire file tabs or Results tab contents to vanish due to not having Undo boundaries/reset
        corrected progress bar showing static middle-percentage progress when RCV Rule searches did not yield matches

-----------------------------------------------------------------------------------------------------------------------------------------------
ver. 1.6
    implemented IO opcodes decoding

    bug fixes and corrections
        corrected auto-selection issue that preserved the previous selection anchor for searches that used a copied word from a double-click selection, that upon using shift + right resulted in unwanted massive selections